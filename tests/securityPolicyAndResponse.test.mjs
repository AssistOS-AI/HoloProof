import test from 'node:test';
import assert from 'node:assert/strict';
import {
  applyTracePolicy,
  buildEvidenceAnchorSet,
  buildVerdictNarrationPrefix,
  validateAnchoredExplanation,
} from '../src/index.mjs';

test('applyTracePolicy redacts model and unsat core fields according to world policy', () => {
  const trace = {
    createdAt: '2026-02-11T10:00:00.000Z',
    solverArtifacts: {
      model: { x: 1, y: 2 },
      unsatCore: ['ax_1', 'ax_2'],
    },
  };

  const policyTrace = applyTracePolicy(trace, {
    sensitivity: 'restricted',
    traceRetentionDays: 7,
    redactModelValues: true,
    allowUnsatCoreDetails: false,
  });

  assert.equal(policyTrace.classification, 'restricted');
  assert.equal(policyTrace.solverArtifacts.model.redacted, true);
  assert.equal(policyTrace.solverArtifacts.unsatCore.redacted, true);
  assert.equal(policyTrace.solverArtifacts.unsatCore.size, 2);
  assert.ok(typeof policyTrace.expiresAt === 'string');
});

test('validateAnchoredExplanation accepts only claims anchored to known evidence', () => {
  const evidence = {
    fragmentIds: ['frag_1'],
    modelKeys: ['x'],
    verdict: 'sat',
  };

  const explanation = {
    claims: [
      {
        text: 'Claim backed by fragment.',
        anchors: [{ type: 'fragment', id: 'frag_1' }],
      },
      {
        text: 'Claim with unknown anchor.',
        anchors: [{ type: 'fragment', id: 'frag_999' }],
      },
    ],
  };

  const result = validateAnchoredExplanation(explanation, evidence, { strict: false });

  assert.equal(result.valid, true);
  assert.equal(result.acceptedClaims.length, 1);
  assert.equal(result.rejectedClaims.length, 1);
  assert.deepEqual([...buildEvidenceAnchorSet(evidence)].sort(), ['fragment:frag_1', 'model:x', 'verdict:sat']);
});

test('buildVerdictNarrationPrefix returns uncertainty framing for unknown verdict', () => {
  const prefix = buildVerdictNarrationPrefix('unknown');
  assert.ok(prefix.toLowerCase().includes('inconclusive'));
});
