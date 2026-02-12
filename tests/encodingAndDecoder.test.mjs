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

test('encodeQueryProposal falls back to registry-aware heuristic when LLM schema is invalid', async () => {
  const encoded = await encodeQueryProposal({
    llmClient: fakeClient(JSON.stringify({
      declarations: [{ name: 'invalid declaration' }],
      assertions: [],
      queryPlan: {
        verificationMode: 'entailment',
        goal: {
          predicate: '???',
          args: [],
        },
      },
      ambiguities: [],
      tags: ['query'],
    })),
    worldId: 'world_main',
    proposalId: 'fp_q3',
    question: 'Is Ana a legal heir?',
    registryContext: {
      symbols: [
        { symbol: 'Ana', kind: 'const', arity: 0, argSorts: [], resultSort: 'Person', usageCount: 10 },
        { symbol: 'legalHeir', kind: 'predicate', arity: 1, argSorts: ['Person'], resultSort: 'Bool', usageCount: 8 },
      ],
      sortAliases: [],
    },
  });

  assert.equal(encoded.ok, true);
  assert.equal(encoded.proposal.queryPlan.goal.op, 'call');
  assert.equal(encoded.proposal.queryPlan.goal.symbol, 'legalHeir');
  assert.equal(encoded.proposal.queryPlan.goal.args[0].name, 'Ana');
  assert.ok(encoded.proposal.tags.includes('heuristic-fallback'));
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

test('decodeResponse uses LLM fast mode for final natural message', async () => {
  const calls = [];
  const llmClient = {
    async complete(request) {
      calls.push(request);
      if (calls.length === 1) {
        return {
          text: JSON.stringify({
            claims: [
              {
                text: 'Anchored claim.',
                anchors: [{ type: 'verdict', id: 'unsat' }],
              },
            ],
          }),
        };
      }
      return {
        text: JSON.stringify({
          message: 'Yes, this is proven by the current rules and facts.',
        }),
      };
    },
  };

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
    llmClient,
    useLLM: true,
    mode: 'deep',
    responseStyle: 'legal',
    queryText: 'Is Ana a legal heir?',
    policy: {
      autoFillWithLLM: false,
    },
  });

  assert.equal(decoded.message, 'Yes, this is proven by the current rules and facts.');
  assert.equal(calls.length, 2);
  assert.equal(calls[0].mode, 'deep');
  assert.equal(calls[1].mode, 'fast');
  assert.ok(calls[1].userPrompt.includes('Requested style: legal'));
});

test('decodeResponse reuses cached natural response for same SMT outcome and question', async () => {
  let calls = 0;
  const llmClient = {
    async complete() {
      calls += 1;
      if (calls % 2 === 1) {
        return {
          text: JSON.stringify({
            claims: [
              {
                text: 'Anchored claim.',
                anchors: [{ type: 'verdict', id: 'unsat' }],
              },
            ],
          }),
        };
      }
      return {
        text: JSON.stringify({
          message: 'Yes, this is proven.',
        }),
      };
    },
  };

  const responseCache = new Map();
  const input = {
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
    llmClient,
    useLLM: true,
    mode: 'fast',
    responseStyle: 'neutral',
    queryText: 'Is Ana a legal heir?',
    responseCache,
    policy: {
      autoFillWithLLM: false,
    },
  };

  const first = await decodeResponse(input);
  const second = await decodeResponse(input);

  assert.equal(first.message, 'Yes, this is proven.');
  assert.equal(second.message, 'Yes, this is proven.');
  assert.equal(calls, 2);
  assert.equal(responseCache.size, 1);
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
