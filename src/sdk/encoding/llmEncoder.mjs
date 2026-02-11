import { FORMAL_PROPOSAL_SCHEMA_VERSION, validateFormalProposal } from '../formalProposal.mjs';
import { sanitizeMetadata, sanitizePromptText } from './promptSanitizer.mjs';
import { parseJsonObject } from './jsonOutput.mjs';

function nowIso(nowFn) {
  return new Date((typeof nowFn === 'function' ? nowFn : Date.now)()).toISOString();
}

function requiredString(value, field) {
  if (typeof value !== 'string' || !value.trim()) {
    throw new Error(`${field} must be a non-empty string.`);
  }
  return value.trim();
}

export function buildFormalizationPrompt(input = {}) {
  const sourceText = sanitizePromptText(input.text || '');
  const source = sanitizeMetadata(input.source || {});
  const registryContext = input.registryContext || { symbols: [], sortAliases: [] };
  const tags = Array.isArray(input.tags) ? input.tags : [];
  const logic = input.logic || 'QF_UF';

  return [
    'You are a formalization transducer for HoloProof.',
    'Return strict JSON object only. No markdown, no prose.',
    'Reuse existing symbols when possible and avoid synonym duplication.',
    `Target logic: ${logic}.`,
    '',
    'Registry context:',
    JSON.stringify(registryContext, null, 2),
    '',
    'Source metadata:',
    JSON.stringify(source, null, 2),
    '',
    'Source text:',
    sourceText,
    '',
    'Output JSON shape:',
    JSON.stringify({
      declarations: [],
      assertions: [],
      queryPlan: { verificationMode: 'entailment', goal: {} },
      ambiguities: [],
      tags,
    }, null, 2),
  ].join('\n');
}

export async function encodeFormalProposal(input = {}) {
  const llmClient = input.llmClient;
  if (!llmClient || typeof llmClient.complete !== 'function') {
    throw new Error('encodeFormalProposal requires llmClient.complete().');
  }

  const worldId = requiredString(input.worldId, 'worldId');
  const proposalId = requiredString(input.proposalId, 'proposalId');
  const sourceId = requiredString(input.sourceId || input.source?.sourceId, 'sourceId');
  const sourceText = requiredString(input.text, 'text');

  const span = input.source?.span || { start: 0, end: sourceText.length };
  const createdAt = input.source?.createdAt || nowIso(input.now);
  const logic = input.logic || 'QF_UF';

  const prompt = buildFormalizationPrompt({
    text: sourceText,
    source: {
      sourceId,
      span,
      createdAt,
    },
    tags: input.tags || [],
    logic,
    registryContext: input.registryContext,
  });

  const completion = await llmClient.complete({
    mode: input.mode || 'fast',
    systemPrompt: 'Return strict JSON only for HoloProof FormalProposal.',
    userPrompt: prompt,
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
        start: Number.isInteger(span.start) ? span.start : 0,
        end: Number.isInteger(span.end) ? span.end : sourceText.length,
      },
      createdAt,
      restrictedProvenance: input.source?.restrictedProvenance === true,
    },
    declarations: Array.isArray(payload.declarations) ? payload.declarations : [],
    assertions: Array.isArray(payload.assertions) ? payload.assertions : [],
    queryPlan: payload.queryPlan || { verificationMode: 'entailment', goal: null },
    ambiguities: Array.isArray(payload.ambiguities) ? payload.ambiguities : [],
    tags: Array.isArray(payload.tags) ? payload.tags : (input.tags || []),
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
