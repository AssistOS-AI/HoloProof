import test from 'node:test';
import assert from 'node:assert/strict';
import {
  DEFAULT_LLM_CACHED_PROFILE,
  REGISTRY_CONTEXT_DISABLED,
  REGISTRY_CONTEXT_STRATEGIES,
  buildCombinations,
  buildSummaryCsv,
  extractCaseIdsFromMarkdown,
  loadCaseIdsFromStructuredCases,
  loadCaseIdsWithFallback,
  loadStructuredCaseDefinitions,
  maybeParseRunnerJson,
  parseRunEvalArgs,
  selectSmokeCases,
  summarizeByCombination,
  summarizeGlobal,
} from '../src/index.mjs';

test('extractCaseIdsFromMarkdown returns unique sorted case IDs', () => {
  const text = 'EV010 EV002 EV002 EV001';
  assert.deepEqual(extractCaseIdsFromMarkdown(text), ['EV001', 'EV002', 'EV010']);
});

test('structured case loaders parse JSON case files and fallback correctly', async () => {
  const definitions = await loadStructuredCaseDefinitions('eval/cases');
  assert.ok(definitions.length > 0);
  assert.ok(definitions.every((item) => /^EV\d{3}$/.test(item.caseId)));

  const caseIds = await loadCaseIdsFromStructuredCases('eval/cases');
  assert.deepEqual(caseIds, definitions.map((item) => item.caseId));

  const fallback = await loadCaseIdsWithFallback({
    casesDir: 'eval/cases',
    planPath: 'docs/specs/DS010-Evaluation-Suite-Plan.md',
  });
  assert.equal(fallback.source, 'structured-plus-plan');
  assert.ok(fallback.caseIds.length >= caseIds.length);
  assert.ok(fallback.caseIds.includes('EV001'));
});

test('selectSmokeCases returns stratified subset when available', () => {
  const all = ['EV001', 'EV005', 'EV011', 'EV017', 'EV021', 'EV024', 'EV031'];
  const selected = selectSmokeCases(all);

  assert.deepEqual(selected, ['EV001', 'EV005', 'EV011', 'EV017', 'EV021', 'EV024', 'EV031']);
});

test('selectSmokeCases falls back to prefix when no stratified cases exist', () => {
  const all = ['EV201', 'EV202', 'EV203'];
  const selected = selectSmokeCases(all, { fallbackSize: 2 });

  assert.deepEqual(selected, ['EV201', 'EV202']);
});

test('buildCombinations builds expected smoke matrix with cached llm profile', () => {
  const combos = buildCombinations('smoke', [DEFAULT_LLM_CACHED_PROFILE], {
    registryContextStrategies: [REGISTRY_CONTEXT_DISABLED],
  });

  assert.equal(combos.length, 4);
  assert.ok(combos.every((combo) => combo.llm.id === 'llm-cached'));
  assert.ok(combos.every((combo) => combo.registryContext.id === 'registry-context-disabled'));
});

test('buildCombinations expands matrix with registry context strategies when enabled', () => {
  const llmProfiles = [
    { id: 'llm-fast-default', mode: 'fast', model: 'fast-a' },
    { id: 'llm-deep-default', mode: 'deep', model: 'deep-a' },
  ];
  const combos = buildCombinations('smoke', llmProfiles, {
    registryContextStrategies: REGISTRY_CONTEXT_STRATEGIES,
  });

  assert.equal(combos.length, 16);
  assert.ok(combos.some((combo) => combo.registryContext.id === 'registry-context-vsa-similarity-topk'));
});

test('parseRunEvalArgs parses key options correctly', () => {
  const args = parseRunEvalArgs(
    ['--mode', 'all', '--llm', '--max-cases', '10', '--smt-cache', 'eval/cache/custom', '--cases-dir', 'eval/cases'],
    { projectRoot: '/workspace/proj' },
  );

  assert.equal(args.mode, 'all');
  assert.equal(args.useLLM, true);
  assert.equal(args.maxCases, 10);
  assert.equal(args.smtCache, '/workspace/proj/eval/cache/custom');
  assert.equal(args.casesDir, '/workspace/proj/eval/cases');
});

test('maybeParseRunnerJson reads the last valid JSON status line', () => {
  const stdout = ['noise', '{"status":"pass","elapsedMs":10}', '{"status":"fail","elapsedMs":4}'].join('\n');
  const parsed = maybeParseRunnerJson(stdout);

  assert.equal(parsed.status, 'fail');
  assert.equal(parsed.elapsedMs, 4);
});

test('summary helpers compute aggregate stats and CSV', () => {
  const combinations = [
    {
      id: 'c1',
      smt: { id: 's1', solver: 'z3' },
      intuition: { id: 'no-intuition' },
      vsa: { id: 'vsa-disabled' },
      registryContext: { id: 'registry-context-disabled' },
      llm: { id: 'llm-cached', mode: 'none', model: 'cached-smt' },
    },
    {
      id: 'c2',
      smt: { id: 's2', solver: 'cvc5' },
      intuition: { id: 'vsa-intuition' },
      vsa: { id: 'vsa-hrr-cosine-topk' },
      registryContext: { id: 'registry-context-usage-topk' },
      llm: { id: 'llm-cached', mode: 'none', model: 'cached-smt' },
    },
  ];

  const records = [
    { combinationId: 'c1', status: 'pass', elapsedMs: 10 },
    { combinationId: 'c1', status: 'pass', elapsedMs: 20 },
    { combinationId: 'c2', status: 'fail', elapsedMs: 30 },
    { combinationId: 'c2', status: 'skipped', elapsedMs: 0 },
  ];

  const byCombination = summarizeByCombination(records, combinations);
  const global = summarizeGlobal(records);

  assert.equal(byCombination.length, 2);
  assert.equal(global.total, 4);
  assert.equal(global.executed, 3);
  assert.equal(global.pass, 2);

  const csv = buildSummaryCsv(byCombination);
  assert.ok(csv.includes('combinationId'));
  assert.ok(csv.includes('c1'));
});
