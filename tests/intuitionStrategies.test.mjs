import test from 'node:test';
import assert from 'node:assert/strict';
import {
  NoIntuitionStrategy,
  VSAIntuitionStrategy,
  createIntuitionStrategy,
} from '../src/index.mjs';

function fragments() {
  return [
    {
      fragmentId: 'frag_001',
      assertionId: 'a1',
      role: 'axiom',
      expr: {
        op: 'call',
        symbol: 'eligible',
        args: [{ op: 'const', name: 'Ana' }],
      },
    },
    {
      fragmentId: 'frag_002',
      assertionId: 'a2',
      role: 'axiom',
      expr: {
        op: 'call',
        symbol: 'blocked',
        args: [{ op: 'const', name: 'Bob' }],
      },
    },
    {
      fragmentId: 'frag_003',
      assertionId: 'a3',
      role: 'axiom',
      expr: {
        op: 'call',
        symbol: 'eligible',
        args: [{ op: 'const', name: 'Bob' }],
      },
    },
  ];
}

test('NoIntuitionStrategy returns deterministic id ordering', () => {
  const strategy = new NoIntuitionStrategy();
  const ranked = strategy.selectCandidates(
    { queryText: 'eligible ana' },
    fragments(),
    { topK: 2 },
  );

  assert.equal(ranked.length, 2);
  assert.deepEqual(
    ranked.map((item) => item.fragmentId),
    ['frag_001', 'frag_002'],
  );
  assert.equal(strategy.explainSelection().strategy, 'no-intuition');
});

test('VSAIntuitionStrategy HRR ranks semantically closer fragments higher', () => {
  const strategy = new VSAIntuitionStrategy({
    representation: 'vsa-hrr-cosine-topk',
    dim: 128,
  });

  strategy.prepare({ fragments: fragments() });
  const ranked = strategy.selectCandidates(
    {
      queryText: 'is Ana eligible',
      goal: { op: 'call', symbol: 'eligible', args: [{ op: 'const', name: 'Ana' }] },
    },
    fragments(),
    { topK: 2 },
  );

  assert.equal(ranked.length, 2);
  assert.equal(ranked[0].fragmentId, 'frag_001');
  assert.equal(strategy.explainSelection().representation, 'vsa-hrr-cosine-topk');
});

test('VSAIntuitionStrategy HDC supports binary hamming ranking', () => {
  const strategy = new VSAIntuitionStrategy({
    representation: 'vsa-hdc-binary-hamming-topk',
    dim: 128,
  });

  const ranked = strategy.selectCandidates(
    {
      queryText: 'blocked bob',
      goal: { op: 'call', symbol: 'blocked', args: [{ op: 'const', name: 'Bob' }] },
    },
    fragments(),
    { topK: 3 },
  );

  assert.equal(ranked.length, 3);
  assert.ok(ranked[0].score >= ranked[1].score);
  assert.equal(strategy.explainSelection().representation, 'vsa-hdc-binary-hamming-topk');
});

test('createIntuitionStrategy builds configured strategy type', () => {
  const noInt = createIntuitionStrategy({ strategy: 'no-intuition' });
  const vsa = createIntuitionStrategy({
    strategy: 'vsa-intuition',
    representation: 'vsa-hrr-cosine-topk',
  });

  assert.ok(noInt instanceof NoIntuitionStrategy);
  assert.ok(vsa instanceof VSAIntuitionStrategy);
});
