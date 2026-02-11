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
  if (reasoning.solverVerdict) {
    claims.push({
      text: `Formal solver verdict: ${reasoning.solverVerdict}.`,
      anchors: [{ type: 'verdict', id: reasoning.solverVerdict }],
    });
  }

  if (evidence.fragmentIds.length > 0) {
    claims.push({
      text: `I used ${evidence.fragmentIds.length} active knowledge fragment(s) from the current world.`,
      anchors: [{ type: 'fragment', id: evidence.fragmentIds[0] }],
    });
  }

  if (evidence.unsatCoreIds.length > 0) {
    claims.push({
      text: `The unsat core cites ${evidence.unsatCoreIds.length} named assertion(s).`,
      anchors: [{ type: 'core', id: evidence.unsatCoreIds[0] }],
    });
  }

  if (evidence.modelKeys.length > 0) {
    claims.push({
      text: `The model includes assignments such as "${evidence.modelKeys[0]}".`,
      anchors: [{ type: 'model', id: evidence.modelKeys[0] }],
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
}

function claimsToText(prefix, claims, fallbackMessage) {
  if (!Array.isArray(claims) || claims.length === 0) {
    return `${prefix} ${fallbackMessage}`.trim();
  }
  const sentence = claims.map((claim) => claim.text).join(' ');
  return `${prefix} ${sentence}`.trim();
}

export async function decodeResponse(input = {}) {
  const reasoning = input.reasoning || {};
  const evidence = buildReasoningEvidence(reasoning);
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
  if (input.useLLM === true && input.llmClient) {
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

  const message = claimsToText(
    decisionContext.narrationPrefix,
    acceptedClaims,
    'No additional anchored explanation is available.',
  );

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
