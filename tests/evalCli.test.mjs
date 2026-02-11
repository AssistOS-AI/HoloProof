import test from 'node:test';
import assert from 'node:assert/strict';
import os from 'node:os';
import path from 'node:path';
import { promises as fs } from 'node:fs';
import { runEvalCli } from '../src/sdk/eval/runEvalCli.mjs';

test('runEvalCli list-only mode returns matrix without executing runner', async () => {
  const tempRoot = await fs.mkdtemp(path.join(os.tmpdir(), 'holoproof-eval-cli-'));
  const planFile = path.join(tempRoot, 'plan.md');

  await fs.writeFile(planFile, '# Plan\n\nEV001 EV005 EV011 EV017 EV021 EV024 EV031 EV034 EV041 EV046 EV051 EV055 EV061 EV066 EV071 EV079 EV081 EV084 EV091 EV098\n', 'utf8');

  const logs = [];
  const logger = {
    log: (line) => logs.push(String(line)),
    warn: (line) => logs.push(String(line)),
    error: (line) => logs.push(String(line)),
  };

  const result = await runEvalCli({
    projectRoot: tempRoot,
    argv: ['--plan', 'plan.md', '--mode', 'smoke', '--list-only'],
    logger,
    env: {},
  });

  assert.equal(result.kind, 'list-only');
  assert.equal(result.cases.length, 20);
  assert.equal(result.combinations.length, 4);
  assert.ok(logs.some((line) => line.includes('dry-run')));

  await fs.rm(tempRoot, { recursive: true, force: true });
});
