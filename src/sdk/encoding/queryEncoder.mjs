import { FORMAL_PROPOSAL_SCHEMA_VERSION, validateFormalProposal } from '../formalProposal.mjs';
import { parseJsonObject } from './jsonOutput.mjs';
import { sanitizePromptText } from './promptSanitizer.mjs';

function nowIso(nowFn) {
  return new Date((typeof nowFn === 'function' ? nowFn : Date.now)()).toISOString();
}

function requiredString(value, field) {
  if (typeof value !== 'string' || !value.trim()) {
    throw new Error(`${field} must be a non-empty string.`);
  }
  return value.trim();
}

function isRecord(value) {
  return value !== null && typeof value === 'object' && !Array.isArray(value);
}

function tokenize(text) {
  return String(text || '')
    .replace(/([a-z0-9])([A-Z])/g, '$1 $2')
    .replace(/_/g, ' ')
    .toLowerCase()
    .split(/[^a-z0-9]+/)
    .filter(Boolean);
}

function overlapScore(leftTokens, rightTokens) {
  if (!Array.isArray(leftTokens) || !Array.isArray(rightTokens)) {
    return 0;
  }
  const left = new Set(leftTokens);
  let score = 0;
  for (const token of rightTokens) {
    if (left.has(token)) {
      score += 1;
    }
  }
  return score;
}

function symbolTokens(symbol, semanticHint = null) {
  return [
    ...tokenize(symbol),
    ...tokenize(semanticHint || ''),
  ];
}

function firstTokenIndex(haystack, needleTokens) {
  if (!Array.isArray(haystack) || !Array.isArray(needleTokens) || needleTokens.length === 0) {
    return -1;
  }
  for (let i = 0; i < haystack.length; i += 1) {
    if (needleTokens.includes(haystack[i])) {
      return i;
    }
  }
  return -1;
}

function tryHeuristicQueryPlan(question, registryContext = {}) {
  const questionTokens = tokenize(question);
  if (questionTokens.length === 0) {
    return null;
  }

  if (questionTokens.includes('consistent') || questionTokens.includes('consistency')) {
    return {
      verificationMode: 'consistency',
      goal: null,
    };
  }

  const symbols = Array.isArray(registryContext.symbols) ? registryContext.symbols : [];
  const predicates = symbols.filter((symbol) => (
    symbol
    && typeof symbol.symbol === 'string'
    && ['predicate', 'function'].includes(String(symbol.kind || '').toLowerCase())
  ));
  const constants = symbols.filter((symbol) => (
    symbol
    && typeof symbol.symbol === 'string'
    && String(symbol.kind || '').toLowerCase() === 'const'
  ));

  let bestPredicate = null;
  let bestScore = 0;
  for (const candidate of predicates) {
    const tokens = symbolTokens(candidate.symbol, candidate.semanticHint);
    const score = overlapScore(questionTokens, tokens);
    if (score > bestScore) {
      bestScore = score;
      bestPredicate = candidate;
    }
  }

  if (!bestPredicate || bestScore <= 0) {
    return null;
  }

  const arity = Number.isInteger(bestPredicate.arity) && bestPredicate.arity >= 0
    ? bestPredicate.arity
    : (Array.isArray(bestPredicate.argSorts) ? bestPredicate.argSorts.length : 0);

  const matchedConstants = constants
    .map((constant) => {
      const tokens = symbolTokens(constant.symbol, constant.semanticHint);
      const score = overlapScore(questionTokens, tokens);
      const index = firstTokenIndex(questionTokens, tokens);
      return {
        symbol: constant.symbol,
        score,
        index,
        usageCount: Number.isInteger(constant.usageCount) ? constant.usageCount : 0,
      };
    })
    .filter((item) => item.score > 0)
    .sort((left, right) => {
      if (left.index !== right.index) {
        return left.index - right.index;
      }
      if (left.score !== right.score) {
        return right.score - left.score;
      }
      if (left.usageCount !== right.usageCount) {
        return right.usageCount - left.usageCount;
      }
      return left.symbol.localeCompare(right.symbol);
    });

  const fallbackConstants = constants
    .map((constant) => ({
      symbol: constant.symbol,
      usageCount: Number.isInteger(constant.usageCount) ? constant.usageCount : 0,
    }))
    .sort((left, right) => {
      if (left.usageCount !== right.usageCount) {
        return right.usageCount - left.usageCount;
      }
      return left.symbol.localeCompare(right.symbol);
    });

  const selectedArgs = [];
  for (const item of matchedConstants) {
    if (selectedArgs.length >= arity) {
      break;
    }
    if (!selectedArgs.includes(item.symbol)) {
      selectedArgs.push(item.symbol);
    }
  }

  for (const item of fallbackConstants) {
    if (selectedArgs.length >= arity) {
      break;
    }
    if (!selectedArgs.includes(item.symbol)) {
      selectedArgs.push(item.symbol);
    }
  }

  if (selectedArgs.length < arity) {
    return null;
  }

  return {
    verificationMode: 'entailment',
    goal: {
      op: 'call',
      symbol: bestPredicate.symbol,
      args: selectedArgs.map((symbol) => ({
        op: 'const',
        name: symbol,
      })),
    },
  };
}

function normalizeExpr(expr) {
  if (!isRecord(expr)) {
    return expr;
  }

  if (typeof expr.op === 'string') {
    const normalized = { ...expr };
    if (Array.isArray(expr.args)) {
      normalized.args = expr.args.map((item) => normalizeExpr(item));
    }
    if (isRecord(expr.arg)) {
      normalized.arg = normalizeExpr(expr.arg);
    }
    if (isRecord(expr.body)) {
      normalized.body = normalizeExpr(expr.body);
    }
    return normalized;
  }

  const callSymbol = expr.predicate || expr.symbol || expr.function;
  if (typeof callSymbol === 'string' && callSymbol.trim()) {
    const args = Array.isArray(expr.args) ? expr.args.map((item) => normalizeExpr(item)) : [];
    return {
      op: 'call',
      symbol: callSymbol.trim(),
      args,
    };
  }

  if (typeof expr.const === 'string' && expr.const.trim()) {
    return {
      op: 'const',
      name: expr.const.trim(),
    };
  }

  if (typeof expr.var === 'string' && expr.var.trim()) {
    return {
      op: 'var',
      name: expr.var.trim(),
    };
  }

  return expr;
}

function normalizeAssertion(assertion) {
  if (!isRecord(assertion)) {
    return assertion;
  }
  return {
    ...assertion,
    expr: normalizeExpr(assertion.expr),
  };
}

function normalizeQueryPlan(queryPlan) {
  if (!isRecord(queryPlan)) {
    return { verificationMode: 'entailment', goal: null };
  }
  return {
    ...queryPlan,
    verificationMode: typeof queryPlan.verificationMode === 'string'
      ? queryPlan.verificationMode
      : 'entailment',
    goal: normalizeExpr(queryPlan.goal),
  };
}

export function buildQueryPrompt(input = {}) {
  const question = sanitizePromptText(input.question || '');
  const registryContext = input.registryContext || { symbols: [], sortAliases: [] };

  return [
    'You are a query encoder for HoloProof.',
    'Return strict JSON only, no markdown.',
    'Do not invent new declarations unless absolutely necessary.',
    '',
    'Question:',
    question,
    '',
    'Registry context:',
    JSON.stringify(registryContext, null, 2),
    '',
    'Output JSON shape:',
    JSON.stringify({
      declarations: [],
      assertions: [],
      queryPlan: { verificationMode: 'entailment', goal: {} },
      ambiguities: [],
      tags: ['query'],
    }, null, 2),
  ].join('\n');
}

export async function encodeQueryProposal(input = {}) {
  const llmClient = input.llmClient;
  if (!llmClient || typeof llmClient.complete !== 'function') {
    throw new Error('encodeQueryProposal requires llmClient.complete().');
  }

  const question = requiredString(input.question, 'question');
  const worldId = requiredString(input.worldId, 'worldId');
  const proposalId = requiredString(input.proposalId, 'proposalId');
  const sourceId = input.sourceId || `query:${proposalId}`;
  const logic = input.logic || 'QF_UF';
  const createdAt = input.createdAt || nowIso(input.now);

  const completion = await llmClient.complete({
    mode: input.mode || 'fast',
    systemPrompt: 'Return strict JSON only for HoloProof query encoding.',
    userPrompt: buildQueryPrompt({
      question,
      registryContext: input.registryContext,
    }),
  });

  const parsed = parseJsonObject(completion?.text || completion);
  if (!parsed.ok) {
    const fallbackPlan = tryHeuristicQueryPlan(question, input.registryContext);
    if (fallbackPlan) {
      const fallbackProposal = {
        schemaVersion: FORMAL_PROPOSAL_SCHEMA_VERSION,
        proposalId,
        worldId,
        logic,
        source: {
          sourceId,
          span: {
            start: 0,
            end: question.length,
          },
          createdAt,
        },
        declarations: [],
        assertions: [],
        queryPlan: fallbackPlan,
        ambiguities: [{
          type: 'heuristic-fallback',
          detail: 'LLM query output was not valid JSON.',
        }],
        tags: ['query', 'heuristic-fallback'],
      };
      const fallbackValidation = validateFormalProposal(fallbackProposal);
      if (fallbackValidation.valid) {
        return {
          ok: true,
          proposal: fallbackProposal,
          errors: [],
          rawText: completion?.text || String(completion || ''),
        };
      }
    }

    return {
      ok: false,
      proposal: null,
      errors: [parsed.error],
      rawText: completion?.text || String(completion || ''),
    };
  }

  const payload = parsed.value;
  const proposal = {
    schemaVersion: FORMAL_PROPOSAL_SCHEMA_VERSION,
    proposalId,
    worldId,
    logic,
    source: {
      sourceId,
      span: {
        start: 0,
        end: question.length,
      },
      createdAt,
    },
    declarations: Array.isArray(payload.declarations) ? payload.declarations : [],
    assertions: Array.isArray(payload.assertions)
      ? payload.assertions.map((assertion) => normalizeAssertion(assertion))
      : [],
    queryPlan: normalizeQueryPlan(payload.queryPlan),
    ambiguities: Array.isArray(payload.ambiguities) ? payload.ambiguities : [],
    tags: Array.isArray(payload.tags) ? payload.tags : ['query'],
  };

  const validation = validateFormalProposal(proposal);
  if (!validation.valid) {
    const fallbackPlan = tryHeuristicQueryPlan(question, input.registryContext);
    if (fallbackPlan) {
      const fallbackProposal = {
        ...proposal,
        declarations: [],
        assertions: [],
        queryPlan: fallbackPlan,
        ambiguities: [{
          type: 'heuristic-fallback',
          detail: 'LLM query output failed schema validation.',
          llmErrors: validation.errors.slice(0, 3),
        }],
        tags: [...new Set([...(Array.isArray(proposal.tags) ? proposal.tags : ['query']), 'heuristic-fallback'])],
      };
      const fallbackValidation = validateFormalProposal(fallbackProposal);
      if (fallbackValidation.valid) {
        return {
          ok: true,
          proposal: fallbackProposal,
          errors: [],
          rawText: completion?.text || String(completion || ''),
        };
      }
    }

    return {
      ok: false,
      proposal,
      errors: validation.errors,
      rawText: completion?.text || String(completion || ''),
    };
  }

  return {
    ok: true,
    proposal,
    errors: [],
    rawText: completion?.text || String(completion || ''),
  };
}
