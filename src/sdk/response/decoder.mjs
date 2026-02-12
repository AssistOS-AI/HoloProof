import { buildResponseDecisionContext } from './decisionPolicy.mjs';
import { parseJsonObject } from '../encoding/jsonOutput.mjs';
import { buildEvidenceAnchorSet, validateAnchoredExplanation } from './evidenceAnchoring.mjs';

function parseModelKeys(modelText) {
  if (typeof modelText !== 'string' || !modelText.trim()) {
    return [];
  }

  const matches = [...modelText.matchAll(/\(define-fun\s+([A-Za-z_][A-Za-z0-9_]*)\s*\(/g)];
  return [...new Set(matches.map((m) => m[1]))];
}

function normalizeUnsatCoreIds(core) {
  if (!Array.isArray(core)) {
    return [];
  }
  return core
    .map((item) => String(item || '').trim())
    .filter(Boolean);
}

function normalizeStringArray(values) {
  if (!Array.isArray(values)) {
    return [];
  }
  return [...new Set(values
    .map((item) => String(item || '').trim())
    .filter(Boolean))]
    .sort();
}

export function buildReasoningEvidence(reasoning = {}) {
  return {
    verdict: reasoning.solverVerdict || 'unknown',
    fragmentIds: Array.isArray(reasoning.activeFragmentIds) ? reasoning.activeFragmentIds : [],
    modelKeys: parseModelKeys(reasoning.model),
    unsatCoreIds: normalizeUnsatCoreIds(reasoning.unsatCore),
  };
}

function defaultClaims(reasoning, evidence) {
  const claims = [];
  if (reasoning.queryVerdict === 'entailed' && reasoning.solverVerdict === 'unsat') {
    claims.push({
      text: 'Yes, the statement is supported by the current rules and facts.',
      anchors: [{ type: 'verdict', id: 'unsat' }],
    });
  } else if (reasoning.queryVerdict === 'not-entailed' && reasoning.solverVerdict === 'sat') {
    claims.push({
      text: 'No, the current rules and facts do not prove that statement.',
      anchors: [{ type: 'verdict', id: 'sat' }],
    });
  } else if (reasoning.solverVerdict === 'unknown') {
    claims.push({
      text: 'The result is still inconclusive with the current reasoning budget.',
      anchors: [{ type: 'verdict', id: 'unknown' }],
    });
  } else if (reasoning.solverVerdict) {
    claims.push({
      text: `The solver verdict is ${reasoning.solverVerdict}.`,
      anchors: [{ type: 'verdict', id: reasoning.solverVerdict }],
    });
  }

  if (evidence.unsatCoreIds.length > 0) {
    claims.push({
      text: 'This conclusion follows from a consistent set of active rules and facts.',
      anchors: [{ type: 'core', id: evidence.unsatCoreIds[0] }],
    });
  } else if (evidence.modelKeys.length > 0) {
    claims.push({
      text: 'A valid model still exists where the statement does not hold.',
      anchors: [{ type: 'model', id: evidence.modelKeys[0] }],
    });
  } else if (evidence.fragmentIds.length > 0) {
    claims.push({
      text: 'The answer is based on the active knowledge loaded in this world.',
      anchors: [{ type: 'fragment', id: evidence.fragmentIds[0] }],
    });
  }

  return claims;
}

async function llmClaims(llmClient, input = {}) {
  if (!llmClient || typeof llmClient.complete !== 'function') {
    return null;
  }

  const prompt = [
    'Generate JSON explanation claims anchored to evidence only.',
    'Return strict JSON object with shape: {"claims":[{"text":"...","anchors":[{"type":"fragment|model|core|verdict","id":"..."}]}]}',
    'Do not invent anchor IDs.',
    '',
    'Evidence:',
    JSON.stringify(input.evidence, null, 2),
    '',
    'Reasoning summary:',
    JSON.stringify({
      verificationMode: input.reasoning?.verificationMode,
      solverVerdict: input.reasoning?.solverVerdict,
      queryVerdict: input.reasoning?.queryVerdict,
      knowledgeGaps: input.reasoning?.knowledgeGaps,
    }, null, 2),
  ].join('\n');

  try {
    const completion = await llmClient.complete({
      mode: input.mode || 'fast',
      systemPrompt: 'Return strict JSON only.',
      userPrompt: prompt,
    });

    const parsed = parseJsonObject(completion?.text || completion);
    if (!parsed.ok) {
      return null;
    }
    return parsed.value;
  } catch {
    return null;
  }
}

function claimsToText(claims, fallbackMessage) {
  if (!Array.isArray(claims) || claims.length === 0) {
    return String(fallbackMessage || '').trim();
  }
  return claims.map((claim) => claim.text).join(' ').trim();
}

function stableSerialize(value) {
  if (value === null || value === undefined) {
    return 'null';
  }
  if (typeof value === 'string') {
    return JSON.stringify(value);
  }
  if (typeof value === 'number' || typeof value === 'boolean') {
    return JSON.stringify(value);
  }
  if (Array.isArray(value)) {
    return `[${value.map((item) => stableSerialize(item)).join(',')}]`;
  }
  if (typeof value === 'object') {
    const keys = Object.keys(value).sort();
    const pairs = keys.map((key) => `${JSON.stringify(key)}:${stableSerialize(value[key])}`);
    return `{${pairs.join(',')}}`;
  }
  return JSON.stringify(String(value));
}

async function cacheGet(cache, key) {
  if (!cache || !key) {
    return null;
  }
  if (cache instanceof Map) {
    return cache.get(key) || null;
  }
  if (typeof cache.get === 'function') {
    const value = await cache.get(key);
    return value ?? null;
  }
  return null;
}

async function cacheSet(cache, key, value) {
  if (!cache || !key) {
    return;
  }
  if (cache instanceof Map) {
    cache.set(key, value);
    return;
  }
  if (typeof cache.set === 'function') {
    await cache.set(key, value);
  }
}

function normalizeResponseStyle(style) {
  const value = String(style || '').trim().toLowerCase();
  if (['neutral', 'legal', 'business', 'casual'].includes(value)) {
    return value;
  }
  return 'neutral';
}

function styleGuidance(style) {
  switch (style) {
    case 'legal':
      return 'Use precise legal wording, clear obligations/entitlements, and avoid slang.';
    case 'business':
      return 'Use executive/business language focused on decision impact and operational clarity.';
    case 'casual':
      return 'Use simple everyday language, short sentences, and approachable tone.';
    default:
      return 'Use balanced neutral language that is clear and professional.';
  }
}

function buildNaturalResponseCacheKey(input = {}) {
  return stableSerialize({
    kind: 'natural-response-v2',
    queryText: String(input.queryText || '').trim(),
    solverVerdict: String(input.solverVerdict || 'unknown'),
    queryVerdict: String(input.queryVerdict || 'unknown'),
    responseStyle: normalizeResponseStyle(input.responseStyle),
    evidence: {
      fragmentIds: normalizeStringArray(input.evidence?.fragmentIds),
      modelKeys: normalizeStringArray(input.evidence?.modelKeys),
      unsatCoreIds: normalizeStringArray(input.evidence?.unsatCoreIds),
    },
  });
}

async function llmNaturalMessage(llmClient, input = {}) {
  if (!llmClient || typeof llmClient.complete !== 'function') {
    return null;
  }

  const safeClaims = Array.isArray(input.claims) ? input.claims : [];
  const responseStyle = normalizeResponseStyle(input.responseStyle);
  const cacheKey = String(input.cacheKey || '').trim() || buildNaturalResponseCacheKey({
    queryText: input.queryText,
    solverVerdict: input.solverVerdict,
    queryVerdict: input.queryVerdict,
    responseStyle,
    evidence: input.evidence,
  });
  const cachedValue = await cacheGet(input.responseCache, cacheKey);
  if (cachedValue && typeof cachedValue.message === 'string' && cachedValue.message.trim()) {
    return cachedValue.message.trim();
  }

  const prompt = [
    'Rewrite the formal result into a natural, human answer for the user.',
    'Constraints:',
    '- Use only the evidence-backed claims listed below.',
    '- Do not mention internal metadata: fragment IDs, unsat core IDs, assertion IDs, world IDs, registry versions, or technical counters.',
    '- Respond in the same language as the user question.',
    '- First sentence must directly answer the question.',
    '- Keep the answer concise (max 4 sentences).',
    `- Requested style: ${responseStyle}. ${styleGuidance(responseStyle)}`,
    '',
    `User question: ${String(input.queryText || '').trim()}`,
    `Solver verdict: ${String(input.solverVerdict || 'unknown')}`,
    `Query verdict: ${String(input.queryVerdict || 'unknown')}`,
    '',
    'Evidence-backed claims:',
    ...safeClaims.map((claim, index) => `${index + 1}. ${claim.text}`),
    '',
    'Return strict JSON only: {"message":"..."}',
  ].join('\n');

  try {
    const completion = await llmClient.complete({
      mode: 'fast',
      systemPrompt: 'Return strict JSON only.',
      userPrompt: prompt,
    });
    const parsed = parseJsonObject(completion?.text || completion);
    if (!parsed.ok || typeof parsed.value?.message !== 'string') {
      return null;
    }
    const message = parsed.value.message.trim();
    if (message) {
      await cacheSet(input.responseCache, cacheKey, {
        message,
        updatedAt: new Date().toISOString(),
      });
    }
    return message || null;
  } catch {
    return null;
  }
}

export async function decodeResponse(input = {}) {
  const reasoning = input.reasoning || {};
  const evidence = buildReasoningEvidence(reasoning);
  const responseStyle = normalizeResponseStyle(input.responseStyle);
  const naturalCacheKey = buildNaturalResponseCacheKey({
    queryText: input.queryText,
    solverVerdict: reasoning.solverVerdict,
    queryVerdict: reasoning.queryVerdict,
    responseStyle,
    evidence,
  });
  let cachedNaturalMessage = null;
  if (input.useLLM === true && input.llmClient) {
    const cached = await cacheGet(input.responseCache || null, naturalCacheKey);
    if (cached && typeof cached.message === 'string' && cached.message.trim()) {
      cachedNaturalMessage = cached.message.trim();
    }
  }
  const decisionContext = input.decisionContext || buildResponseDecisionContext({
    solverOutcome: {
      verdict: reasoning.solverVerdict,
      timeout: reasoning.timeout,
    },
    knowledgeGaps: reasoning.knowledgeGaps,
    policy: input.policy || {},
    llmAvailable: Boolean(input.llmClient),
  });

  const defaultExplanation = {
    claims: defaultClaims(reasoning, evidence),
  };

  let candidate = defaultExplanation;
  if (!cachedNaturalMessage && input.useLLM === true && input.llmClient) {
    const generated = await llmClaims(input.llmClient, {
      evidence,
      reasoning,
      mode: input.mode,
    });
    if (generated && typeof generated === 'object') {
      candidate = generated;
    }
  }

  const validated = validateAnchoredExplanation(candidate, evidence, { strict: false });
  const acceptedClaims = validated.acceptedClaims.length > 0
    ? validated.acceptedClaims
    : defaultExplanation.claims;

  let message = claimsToText(
    acceptedClaims,
    'I could not generate a fuller explanation, but this answer is still solver-backed.',
  );

  if (cachedNaturalMessage) {
    message = cachedNaturalMessage;
  } else if (input.useLLM === true && input.llmClient) {
    const natural = await llmNaturalMessage(input.llmClient, {
      queryText: input.queryText,
      solverVerdict: reasoning.solverVerdict,
      queryVerdict: reasoning.queryVerdict,
      claims: acceptedClaims,
      responseStyle,
      evidence,
      cacheKey: naturalCacheKey,
      responseCache: input.responseCache || null,
    });
    if (natural) {
      message = natural;
    }
  }

  return {
    action: decisionContext.decision.action,
    reason: decisionContext.decision.reason,
    solverVerdict: reasoning.solverVerdict || 'unknown',
    queryVerdict: reasoning.queryVerdict || 'unknown',
    message,
    claims: acceptedClaims,
    rejectedClaims: validated.rejectedClaims,
    questions: decisionContext.decision.questions || [],
    surfacedIssues: decisionContext.surfacedIssues || [],
    evidenceAnchors: [...buildEvidenceAnchorSet(evidence)],
  };
}
