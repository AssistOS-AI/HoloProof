import { collectReferencedSymbols } from '../formalProposal.mjs';
import { decideExpansion } from './expansionPolicy.mjs';
import { emitAssertionSmt, emitNegatedGoalAssertion } from '../solver/smtEmitter.mjs';

function positiveInteger(value, fallback) {
  return Number.isInteger(value) && value > 0 ? value : fallback;
}

function normalizeMode(mode) {
  const allowed = new Set(['entailment', 'model-finding', 'consistency']);
  return allowed.has(mode) ? mode : 'entailment';
}

function toFragmentAssertion(fragment) {
  return {
    assertionId: `hp_frag_${fragment.fragmentId}`,
    expr: fragment.expr,
  };
}

function uniqueSorted(values) {
  return [...new Set(values)].sort();
}

function collectSymbolsFromFragments(fragments) {
  const symbolToFragmentIds = new Map();
  for (const fragment of fragments) {
    const symbols = collectReferencedSymbols(fragment.expr);
    for (const symbol of symbols) {
      if (!symbolToFragmentIds.has(symbol)) {
        symbolToFragmentIds.set(symbol, []);
      }
      symbolToFragmentIds.get(symbol).push(fragment.fragmentId);
    }
  }

  for (const [symbol, fragmentIds] of symbolToFragmentIds.entries()) {
    symbolToFragmentIds.set(symbol, uniqueSorted(fragmentIds));
  }

  return symbolToFragmentIds;
}

export function detectKnowledgeGaps({ queryPlan, activeFragments, registryEntries = [] }) {
  const goalSymbols = collectReferencedSymbols(queryPlan?.goal || {});
  const registrySymbols = new Set((registryEntries || []).map((entry) => entry.symbol));
  const symbolUsage = collectSymbolsFromFragments(activeFragments || []);

  const missingSymbols = [];
  const lowSupportSymbols = [];
  const missingEvidence = [];

  for (const symbol of goalSymbols) {
    if (!registrySymbols.has(symbol)) {
      missingSymbols.push(symbol);
      missingEvidence.push({
        type: 'missing-registry-symbol',
        symbol,
        message: `Symbol "${symbol}" is missing from world registry.`,
      });
      continue;
    }

    const supportingFragments = symbolUsage.get(symbol) || [];
    if (supportingFragments.length === 0) {
      lowSupportSymbols.push(symbol);
      missingEvidence.push({
        type: 'no-supporting-fragment',
        symbol,
        message: `No active fragment currently supports symbol "${symbol}".`,
      });
    }
  }

  return {
    goalSymbols: uniqueSorted(goalSymbols),
    missingSymbols: uniqueSorted(missingSymbols),
    lowSupportSymbols: uniqueSorted(lowSupportSymbols),
    missingEvidence,
    hasGaps: missingEvidence.length > 0,
  };
}

function orderFragments(fragments, rankedFragmentIds = null) {
  const byId = new Map((fragments || []).map((fragment) => [fragment.fragmentId, fragment]));

  const ranked = Array.isArray(rankedFragmentIds)
    ? rankedFragmentIds.filter((fragmentId) => byId.has(fragmentId)).map((fragmentId) => byId.get(fragmentId))
    : [];

  const rankedIds = new Set(ranked.map((fragment) => fragment.fragmentId));
  const leftovers = (fragments || [])
    .filter((fragment) => !rankedIds.has(fragment.fragmentId))
    .sort((left, right) => left.fragmentId.localeCompare(right.fragmentId));

  return [...ranked, ...leftovers];
}

function applyIntuitionRanking({
  intuition,
  queryPlan,
  fragments,
  budget,
}) {
  if (!intuition || typeof intuition.selectCandidates !== 'function') {
    return {
      rankedFragmentIds: null,
      diagnostics: null,
    };
  }

  const topK = positiveInteger(budget.maxActiveAtoms, fragments.length || 1);
  const selection = intuition.selectCandidates(
    {
      goal: queryPlan?.goal || null,
      verificationMode: queryPlan?.verificationMode || 'entailment',
      queryText: queryPlan?.queryText || '',
    },
    fragments,
    { topK },
  );

  const rankedFragmentIds = Array.isArray(selection)
    ? selection.map((item) => item.fragmentId).filter(Boolean)
    : [];

  const diagnostics = typeof intuition.explainSelection === 'function'
    ? intuition.explainSelection()
    : null;

  return {
    rankedFragmentIds,
    diagnostics,
  };
}

async function runSingleRound({ solverAdapter, sessionId, verificationMode, goal, activeFragments, timeoutMs }) {
  await solverAdapter.push(sessionId);

  try {
    for (const fragment of activeFragments) {
      await solverAdapter.assert(sessionId, emitAssertionSmt(toFragmentAssertion(fragment), { named: true }), {
        scope: 'transient',
      });
    }

    if (verificationMode === 'entailment') {
      await solverAdapter.assert(sessionId, emitNegatedGoalAssertion(goal, 'hp_query_negated_goal'), {
        scope: 'transient',
      });
    } else if (verificationMode === 'model-finding') {
      await solverAdapter.assert(sessionId, emitAssertionSmt({
        assertionId: 'hp_query_goal',
        expr: goal,
      }, { named: false }), { scope: 'transient' });
    }

    const check = await solverAdapter.checkSat(sessionId, { timeoutMs });
    let queryVerdict = 'unknown';

    if (verificationMode === 'entailment') {
      if (check.verdict === 'unsat') {
        queryVerdict = 'entailed';
      } else if (check.verdict === 'sat') {
        queryVerdict = 'not-entailed';
      }
    } else if (verificationMode === 'model-finding') {
      if (check.verdict === 'sat') {
        queryVerdict = 'model-found';
      } else if (check.verdict === 'unsat') {
        queryVerdict = 'no-model';
      }
    } else if (verificationMode === 'consistency') {
      if (check.verdict === 'sat') {
        queryVerdict = 'consistent';
      } else if (check.verdict === 'unsat') {
        queryVerdict = 'inconsistent';
      }
    }

    let model = null;
    let unsatCore = null;

    if (check.verdict === 'sat') {
      model = await solverAdapter.getModel(sessionId);
    } else if (check.verdict === 'unsat') {
      unsatCore = await solverAdapter.getUnsatCore(sessionId);
    }

    return {
      solverVerdict: check.verdict,
      queryVerdict,
      timeout: check.timeout === true,
      recovered: check.recovered === true,
      elapsedMs: check.elapsedMs,
      model,
      unsatCore,
    };
  } finally {
    await solverAdapter.pop(sessionId, 1);
  }
}

export async function runReasoningQuery(options = {}) {
  const {
    solverAdapter,
    sessionId,
    queryPlan,
    fragments = [],
    rankedFragmentIds = null,
    registryEntries = [],
    budget = {},
  } = options;

  if (!solverAdapter || typeof solverAdapter.checkSat !== 'function') {
    throw new Error('runReasoningQuery requires a solverAdapter with checkSat support.');
  }

  if (!sessionId) {
    throw new Error('runReasoningQuery requires sessionId.');
  }

  const verificationMode = normalizeMode(queryPlan?.verificationMode);
  const goal = queryPlan?.goal || null;

  if (verificationMode !== 'consistency' && !goal) {
    throw new Error(`Query mode "${verificationMode}" requires queryPlan.goal.`);
  }

  const intuitionRanking = !rankedFragmentIds
    ? applyIntuitionRanking({
      intuition: options.intuition || null,
      queryPlan,
      fragments,
      budget,
    })
    : {
      rankedFragmentIds: null,
      diagnostics: null,
    };

  const ordered = orderFragments(
    fragments,
    rankedFragmentIds || intuitionRanking.rankedFragmentIds || null,
  );

  const maxRounds = positiveInteger(budget.maxExpansionRounds, 3);
  const expansionStep = positiveInteger(budget.expansionStep, Math.max(1, Math.min(25, ordered.length)));
  const maxActiveAtoms = positiveInteger(budget.maxActiveAtoms, ordered.length || 1);
  const timeoutMs = positiveInteger(budget.timeoutMs, 4000);

  let activeCount = Math.min(Math.max(1, expansionStep), Math.min(maxActiveAtoms, ordered.length || 1));
  let previousRound = null;
  let round = 1;
  const rounds = [];

  while (round <= maxRounds) {
    const cappedActiveCount = Math.min(activeCount, maxActiveAtoms, ordered.length);
    const activeFragments = ordered.slice(0, cappedActiveCount);
    const activeFragmentIds = activeFragments.map((fragment) => fragment.fragmentId);
    const knowledgeGaps = detectKnowledgeGaps({
      queryPlan,
      activeFragments,
      registryEntries,
    });

    const roundResult = await runSingleRound({
      solverAdapter,
      sessionId,
      verificationMode,
      goal,
      activeFragments,
      timeoutMs,
    });

    rounds.push({
      round,
      activeCount: cappedActiveCount,
      activeFragmentIds,
      knowledgeGaps,
      ...roundResult,
    });

    if (roundResult.solverVerdict !== 'unknown') {
      break;
    }

    const expansionDecision = decideExpansion({
      round,
      maxRounds,
      expansionStep,
      remainingCandidates: Math.max(0, Math.min(maxActiveAtoms, ordered.length) - cappedActiveCount),
      currentVerdict: roundResult.solverVerdict,
      previousVerdict: previousRound?.solverVerdict ?? null,
      previousActiveCount: previousRound?.activeCount ?? null,
      currentActiveCount: cappedActiveCount,
    });

    if (expansionDecision.action !== 'expand') {
      break;
    }

    activeCount = cappedActiveCount + expansionDecision.nextAddCount;
    previousRound = rounds[rounds.length - 1];
    round += 1;
  }

  const finalRound = rounds[rounds.length - 1] || {
    solverVerdict: 'unknown',
    queryVerdict: 'unknown',
    timeout: false,
    elapsedMs: 0,
    model: null,
    unsatCore: null,
    activeFragmentIds: [],
    knowledgeGaps: detectKnowledgeGaps({
      queryPlan,
      activeFragments: [],
      registryEntries,
    }),
  };

  return {
    verificationMode,
    solverVerdict: finalRound.solverVerdict,
    queryVerdict: finalRound.queryVerdict,
    timeout: finalRound.timeout,
    model: finalRound.model,
    unsatCore: finalRound.unsatCore,
    activeFragmentIds: finalRound.activeFragmentIds,
    knowledgeGaps: finalRound.knowledgeGaps,
    rounds,
    intuition: {
      used: Boolean(options.intuition),
      diagnostics: intuitionRanking.diagnostics,
      rankedFragmentIds: intuitionRanking.rankedFragmentIds || rankedFragmentIds || null,
    },
    totalElapsedMs: rounds.reduce((sum, item) => sum + (item.elapsedMs || 0), 0),
  };
}
