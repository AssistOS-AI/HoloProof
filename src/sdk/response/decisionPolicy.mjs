import { buildVerdictNarrationPrefix } from './evidenceAnchoring.mjs';

function positiveInteger(value, fallback) {
  return Number.isInteger(value) && value > 0 ? value : fallback;
}

function normalizePolicy(policy = {}) {
  return {
    autoFillWithLLM: policy.autoFillWithLLM === true,
    llmAutoFillMaxSymbols: positiveInteger(policy.llmAutoFillMaxSymbols, 2),
    llmAutoFillMaxMissingEvidence: positiveInteger(policy.llmAutoFillMaxMissingEvidence, 2),
    preferUserClarification: policy.preferUserClarification !== false,
    askOnUnknownVerdict: policy.askOnUnknownVerdict === true,
  };
}

function normalizeKnowledgeGaps(gaps = {}) {
  const missingSymbols = Array.isArray(gaps.missingSymbols) ? [...new Set(gaps.missingSymbols)] : [];
  const lowSupportSymbols = Array.isArray(gaps.lowSupportSymbols) ? [...new Set(gaps.lowSupportSymbols)] : [];
  const missingEvidence = Array.isArray(gaps.missingEvidence) ? gaps.missingEvidence.slice() : [];

  return {
    missingSymbols,
    lowSupportSymbols,
    missingEvidence,
    hasGaps: missingSymbols.length > 0 || lowSupportSymbols.length > 0 || missingEvidence.length > 0,
  };
}

function buildQuestions(gaps, solverOutcome) {
  const questions = [];

  for (const symbol of gaps.missingSymbols) {
    questions.push(`Please define symbol "${symbol}" or provide a statement that declares it.`);
  }

  for (const symbol of gaps.lowSupportSymbols) {
    questions.push(`I need at least one supporting fact/axiom for "${symbol}". Can you provide one?`);
  }

  if (solverOutcome?.error && typeof solverOutcome.error === 'string') {
    questions.push(`Solver reported: ${solverOutcome.error}. Please confirm if I should retry with adjusted constraints.`);
  }

  if (solverOutcome?.verdict === 'unknown') {
    questions.push('The solver returned "unknown". Should I try a broader knowledge slice or a different strategy?');
  }

  return questions;
}

export function decideGapAction(input = {}) {
  const policy = normalizePolicy(input.policy);
  const gaps = normalizeKnowledgeGaps(input.knowledgeGaps);
  const solverOutcome = input.solverOutcome || {};
  const llmAvailable = input.llmAvailable === true;

  const surfacedIssues = [];
  if (gaps.missingSymbols.length > 0) {
    surfacedIssues.push({
      code: 'missing-symbols',
      level: 'error',
      symbols: gaps.missingSymbols,
    });
  }
  if (gaps.lowSupportSymbols.length > 0) {
    surfacedIssues.push({
      code: 'missing-facts',
      level: 'warning',
      symbols: gaps.lowSupportSymbols,
    });
  }
  if (solverOutcome?.error) {
    surfacedIssues.push({
      code: 'solver-error',
      level: 'error',
      message: solverOutcome.error,
    });
  }
  if (solverOutcome?.timeout === true) {
    surfacedIssues.push({
      code: 'solver-timeout',
      level: 'warning',
      message: 'Solver reached configured timeout.',
    });
  }

  if (solverOutcome?.error) {
    return {
      action: 'ask-user',
      reason: 'solver-error',
      surfacedIssues,
      questions: buildQuestions(gaps, solverOutcome),
      llmAutofillPlan: null,
    };
  }

  if (gaps.hasGaps) {
    const canAutofill = policy.autoFillWithLLM
      && llmAvailable
      && gaps.missingSymbols.length <= policy.llmAutoFillMaxSymbols
      && gaps.missingEvidence.length <= policy.llmAutoFillMaxMissingEvidence
      && !policy.preferUserClarification;

    if (canAutofill) {
      return {
        action: 'llm-autofill',
        reason: 'kb-gaps-autofill',
        surfacedIssues,
        questions: [],
        llmAutofillPlan: {
          missingSymbols: gaps.missingSymbols,
          missingEvidence: gaps.missingEvidence,
        },
      };
    }

    return {
      action: 'ask-user',
      reason: 'kb-gaps-need-clarification',
      surfacedIssues,
      questions: buildQuestions(gaps, solverOutcome),
      llmAutofillPlan: null,
    };
  }

  if (solverOutcome?.verdict === 'unknown' && policy.askOnUnknownVerdict) {
    return {
      action: 'ask-user',
      reason: 'unknown-verdict',
      surfacedIssues,
      questions: buildQuestions(gaps, solverOutcome),
      llmAutofillPlan: null,
    };
  }

  return {
    action: 'answer',
    reason: 'sufficient-evidence',
    surfacedIssues,
    questions: [],
    llmAutofillPlan: null,
  };
}

export function buildResponseDecisionContext(input = {}) {
  const decision = decideGapAction(input);
  const solverOutcome = input.solverOutcome || {};

  return {
    decision,
    narrationPrefix: buildVerdictNarrationPrefix(solverOutcome.verdict),
    solverVerdict: solverOutcome.verdict || 'unknown',
    surfacedIssues: decision.surfacedIssues,
  };
}
