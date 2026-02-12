import test from 'node:test';
import assert from 'node:assert/strict';
import { DEMO_SCENARIOS } from '../chat/demo-scenarios.mjs';
import { buildKnowledgePreview, buildKnowledgeSummary } from '../chat/server/scenarioKnowledgeView.mjs';

test('scenario knowledge preview contains concrete declarations and assertions', () => {
  const scenario = DEMO_SCENARIOS.find((item) => item.id === 'family-inheritance');
  assert.ok(scenario, 'family-inheritance scenario must exist');

  const preview = buildKnowledgePreview(scenario);
  assert.ok(preview.some((line) => line.includes('Maria is a Person')));
  assert.ok(preview.some((line) => line.includes('Ana is child of Maria')));
  assert.equal(preview.some((line) => line.includes('proposal ') || line.includes('assertion:') || line.includes('declaration:')), false);
});

test('scenario knowledge summary still counts proposals, declarations, and assertions', () => {
  const scenario = DEMO_SCENARIOS.find((item) => item.id === 'family-inheritance');
  assert.ok(scenario, 'family-inheritance scenario must exist');

  const summary = buildKnowledgeSummary(scenario);
  assert.deepEqual(summary, {
    proposals: 1,
    declarations: 5,
    assertions: 2,
  });
});
