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
