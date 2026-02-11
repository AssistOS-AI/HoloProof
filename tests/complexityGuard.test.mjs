import test from 'node:test';
import assert from 'node:assert/strict';
import {
  checkComplexityBudget,
  evaluateReasoningComplexity,
  runReasoningQuery,
} from '../src/index.mjs';

function bigExpr(depth) {
  if (depth <= 0) {
    return { op: 'const', name: 'Ana' };
  }
  return {
    op: 'and',
    args: [bigExpr(depth - 1), bigExpr(depth - 1)],
  };
}

test('complexity guard computes metrics and detects violations', () => {
  const metrics = evaluateReasoningComplexity({
    queryPlan: {
      goal: bigExpr(5),
    },
    fragments: [
      { expr: bigExpr(4) },
    ],
  });

  assert.ok(metrics.totalNodes > 0);
  const check = checkComplexityBudget(metrics, {
    maxTotalNodes: 20,
    maxQuantifiers: 10,
    maxExprDepth: 6,
  });
  assert.equal(check.ok, false);
  assert.ok(check.violations.length > 0);
});

test('runReasoningQuery returns unknown when complexity budget is exceeded', async () => {
  const solver = {
    async push() {},
    async pop() {},
    async assert() {},
    async checkSat() { return { verdict: 'sat', elapsedMs: 1, timeout: false }; },
    async getModel() { return null; },
    async getUnsatCore() { return null; },
  };

  const fragments = [];
  for (let i = 0; i < 3; i += 1) {
    fragments.push({
      fragmentId: `frag_${i}`,
      expr: bigExpr(6),
    });
  }

  const result = await runReasoningQuery({
    solverAdapter: solver,
    sessionId: 's1',
    queryPlan: {
      verificationMode: 'entailment',
      goal: bigExpr(6),
    },
    fragments,
    registryEntries: [],
    budget: {
      maxTotalNodes: 30,
      maxQuantifiers: 5,
      maxExprDepth: 10,
    },
  });

  assert.equal(result.solverVerdict, 'unknown');
  assert.equal(result.complexityGuard.ok, false);
  assert.ok(result.complexityGuard.violations.length > 0);
});
