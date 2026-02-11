import test from 'node:test';
import assert from 'node:assert/strict';
import {
  buildFormalizationPrompt,
  buildQueryPrompt,
  createAchillesLLMClient,
  decodeResponse,
  encodeFormalProposal,
  encodeQueryProposal,
  parseJsonObject,
  sanitizePromptText,
} from '../src/index.mjs';

function fakeClient(responseText) {
  return {
    async complete() {
      return {
        text: responseText,
      };
    },
  };
}

test('sanitizePromptText removes control chars and truncates', () => {
  const input = `Hello\u0000World\n\n\nNext`;
  const cleaned = sanitizePromptText(input, { maxLength: 12 });
  assert.equal(cleaned, 'Hello World\n');
});

test('parseJsonObject extracts JSON from mixed output', () => {
  const parsed = parseJsonObject('noise {"a":1,"b":2} tail');
  assert.equal(parsed.ok, true);
  assert.equal(parsed.value.a, 1);
});

test('encodeFormalProposal validates strict FormalProposal shape', async () => {
  const response = JSON.stringify({
    declarations: [
      { kind: 'sort', name: 'Person' },
      { kind: 'const', name: 'Ana', resultSort: 'Person' },
      { kind: 'predicate', name: 'eligible', argSorts: ['Person'], resultSort: 'Bool' },
    ],
    assertions: [
      {
        assertionId: 'ax_1',
        role: 'fact',
        expr: { op: 'call', symbol: 'eligible', args: [{ op: 'const', name: 'Ana' }] },
      },
    ],
    queryPlan: {
      verificationMode: 'entailment',
      goal: { op: 'call', symbol: 'eligible', args: [{ op: 'const', name: 'Ana' }] },
    },
    ambiguities: [],
    tags: ['test'],
  });

  const encoded = await encodeFormalProposal({
    llmClient: fakeClient(response),
    worldId: 'world_main',
    proposalId: 'fp_1001',
    sourceId: 'doc_1',
    text: 'Ana is eligible.',
    logic: 'QF_UF',
  });

  assert.equal(encoded.ok, true);
  assert.equal(encoded.proposal.logic, 'QF_UF');
  assert.equal(encoded.proposal.schemaVersion, 'holoproof.formal-proposal.v1');
});

test('encodeQueryProposal returns invalid when LLM response is malformed', async () => {
  const encoded = await encodeQueryProposal({
    llmClient: fakeClient('not json'),
    worldId: 'world_main',
    proposalId: 'fp_q1',
    question: 'Is Ana eligible?',
  });

  assert.equal(encoded.ok, false);
  assert.ok(encoded.errors[0].toLowerCase().includes('json'));
});

test('encodeQueryProposal normalizes shorthand goal expressions from LLM output', async () => {
  const encoded = await encodeQueryProposal({
    llmClient: fakeClient(JSON.stringify({
      declarations: [],
      assertions: [],
      queryPlan: {
        verificationMode: 'entailment',
        goal: {
          predicate: 'legalHeir',
          args: [{ const: 'Ana' }],
        },
      },
      ambiguities: [],
      tags: ['query'],
    })),
    worldId: 'world_main',
    proposalId: 'fp_q2',
    question: 'Is Ana a legal heir?',
  });

  assert.equal(encoded.ok, true);
  assert.equal(encoded.proposal.queryPlan.goal.op, 'call');
  assert.equal(encoded.proposal.queryPlan.goal.symbol, 'legalHeir');
  assert.equal(encoded.proposal.queryPlan.goal.args[0].op, 'const');
  assert.equal(encoded.proposal.queryPlan.goal.args[0].name, 'Ana');
});

test('decodeResponse filters unanchored claims and keeps anchored defaults', async () => {
  const decoded = await decodeResponse({
    reasoning: {
      solverVerdict: 'unsat',
      queryVerdict: 'entailed',
      activeFragmentIds: ['frag_001'],
      unsatCore: ['core_1'],
      model: null,
      knowledgeGaps: {
        missingSymbols: [],
        lowSupportSymbols: [],
        missingEvidence: [],
      },
    },
    llmClient: fakeClient(JSON.stringify({
      claims: [
        {
          text: 'Anchored claim.',
          anchors: [{ type: 'core', id: 'core_1' }],
        },
        {
          text: 'Unanchored claim.',
          anchors: [{ type: 'core', id: 'missing' }],
        },
      ],
    })),
    useLLM: true,
    policy: {
      autoFillWithLLM: false,
    },
  });

  assert.equal(decoded.action, 'answer');
  assert.ok(decoded.claims.some((claim) => claim.text.includes('Anchored')));
  assert.ok(decoded.rejectedClaims.length >= 1);
});

test('createAchillesLLMClient supports injectable client and import fallback', async () => {
  const direct = await createAchillesLLMClient({
    client: { complete: async () => ({ text: 'ok' }) },
  });
  assert.ok(direct);

  const missing = await createAchillesLLMClient({
    importAchilles: async () => null,
  });
  assert.equal(missing, null);
});

test('prompt builders include registry context and question text', () => {
  const formalPrompt = buildFormalizationPrompt({
    text: 'Ana is eligible',
    source: { sourceId: 'doc_1' },
    registryContext: { symbols: [{ symbol: 'eligible' }] },
  });
  const queryPrompt = buildQueryPrompt({
    question: 'Is Ana eligible?',
    registryContext: { symbols: [{ symbol: 'eligible' }] },
  });

  assert.ok(formalPrompt.includes('Registry context'));
  assert.ok(queryPrompt.includes('Question'));
});
