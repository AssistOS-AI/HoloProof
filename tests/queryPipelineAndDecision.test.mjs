import test from 'node:test';
import assert from 'node:assert/strict';
import {
  buildResponseDecisionContext,
  decideGapAction,
  executeFormalQueryPipeline,
  runReasoningQuery,
} from '../src/index.mjs';

function buildFakeSolver(verdicts) {
  const queue = verdicts.slice();
  const commands = [];

  return {
    async push() {
      commands.push('push');
    },
    async pop() {
      commands.push('pop');
    },
    async assert(_sessionId, assertion) {
      commands.push(`assert:${String(assertion).slice(0, 30)}`);
    },
    async checkSat() {
      const next = queue.shift() || { verdict: 'unknown', elapsedMs: 1 };
      commands.push(`check:${next.verdict}`);
      return {
        verdict: next.verdict,
        elapsedMs: next.elapsedMs || 1,
        timeout: next.timeout === true,
        recovered: next.recovered === true,
      };
    },
    async getModel() {
      commands.push('get-model');
      return '(model (define-fun witness () Int 1))';
    },
    async getUnsatCore() {
      commands.push('get-unsat-core');
      return ['hp_frag_frag_001'];
    },
    commands,
  };
}

function baseFragments() {
  return [
    {
      fragmentId: 'frag_001',
      expr: {
        op: 'forall',
        vars: [{ name: 'x', sort: 'Person' }],
        body: {
          op: '=>',
          args: [
            { op: 'call', symbol: 'student', args: [{ op: 'var', name: 'x' }] },
            { op: 'call', symbol: 'eligible', args: [{ op: 'var', name: 'x' }] },
          ],
        },
      },
    },
    {
      fragmentId: 'frag_002',
      expr: {
        op: 'call',
        symbol: 'student',
        args: [{ op: 'const', name: 'Ana' }],
      },
    },
  ];
}

function registryEntries() {
  return [
    { symbol: 'Person' },
    { symbol: 'student' },
    { symbol: 'eligible' },
    { symbol: 'Ana' },
  ];
}

test('runReasoningQuery expands active fragments when verdict remains unknown', async () => {
  const solver = buildFakeSolver([
    { verdict: 'unknown', elapsedMs: 5 },
    { verdict: 'unsat', elapsedMs: 7 },
  ]);

  const result = await runReasoningQuery({
    solverAdapter: solver,
    sessionId: 's1',
    queryPlan: {
      verificationMode: 'entailment',
      goal: { op: 'call', symbol: 'eligible', args: [{ op: 'const', name: 'Ana' }] },
    },
    fragments: baseFragments(),
    registryEntries: registryEntries(),
    budget: {
      maxExpansionRounds: 3,
      expansionStep: 1,
      maxActiveAtoms: 2,
      timeoutMs: 100,
    },
  });

  assert.equal(result.rounds.length, 2);
  assert.equal(result.rounds[0].activeCount, 1);
  assert.equal(result.rounds[1].activeCount, 2);
  assert.equal(result.solverVerdict, 'unsat');
  assert.equal(result.queryVerdict, 'entailed');
});

test('decideGapAction can choose llm-autofill for small KB gaps', () => {
  const decision = decideGapAction({
    solverOutcome: { verdict: 'unknown' },
    knowledgeGaps: {
      missingSymbols: ['income'],
      lowSupportSymbols: [],
      missingEvidence: [{ type: 'missing-registry-symbol', symbol: 'income' }],
    },
    llmAvailable: true,
    policy: {
      autoFillWithLLM: true,
      preferUserClarification: false,
      llmAutoFillMaxSymbols: 2,
      llmAutoFillMaxMissingEvidence: 2,
    },
  });

  assert.equal(decision.action, 'llm-autofill');
  assert.equal(decision.reason, 'kb-gaps-autofill');
  assert.deepEqual(decision.llmAutofillPlan.missingSymbols, ['income']);
});

test('buildResponseDecisionContext requests clarification when KB gaps remain', () => {
  const context = buildResponseDecisionContext({
    solverOutcome: { verdict: 'sat' },
    knowledgeGaps: {
      missingSymbols: ['policyRule'],
      lowSupportSymbols: [],
      missingEvidence: [{ type: 'missing-registry-symbol', symbol: 'policyRule' }],
    },
    llmAvailable: false,
    policy: {
      autoFillWithLLM: true,
      preferUserClarification: true,
    },
  });

  assert.equal(context.decision.action, 'ask-user');
  assert.ok(context.decision.questions.some((question) => question.includes('policyRule')));
});

test('executeFormalQueryPipeline returns reasoning plus response decision', async () => {
  const solver = buildFakeSolver([{ verdict: 'sat', elapsedMs: 3 }]);

  const run = await executeFormalQueryPipeline({
    solverAdapter: solver,
    sessionId: 's1',
    queryPlan: {
      verificationMode: 'model-finding',
      goal: { op: 'call', symbol: 'eligible', args: [{ op: 'const', name: 'Ana' }] },
    },
    fragments: baseFragments(),
    registryEntries: registryEntries(),
    budget: {
      maxExpansionRounds: 1,
      expansionStep: 2,
      maxActiveAtoms: 2,
      timeoutMs: 100,
    },
    llmAvailable: true,
    decoderPolicy: {
      autoFillWithLLM: true,
      preferUserClarification: false,
    },
  });

  assert.equal(run.reasoning.solverVerdict, 'sat');
  assert.equal(run.response.decision.action, 'answer');
  assert.ok(run.response.narrationPrefix.toLowerCase().includes('solver evidence'));
});
