#!/usr/bin/env node

import { runEvalCli } from '../src/sdk/eval/runEvalCli.mjs';

runEvalCli({
  argv: process.argv.slice(2),
  env: process.env,
  logger: console,
}).catch((error) => {
  console.error(`[runEval] Fatal: ${error.message}`);
  process.exitCode = 1;
});
