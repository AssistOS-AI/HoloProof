#!/usr/bin/env node

import { promises as fs } from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { spawn } from 'node:child_process';
import { performance } from 'node:perf_hooks';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);
const PROJECT_ROOT = path.resolve(__dirname, '..');

const DEFAULT_PLAN_PATH = path.resolve(PROJECT_ROOT, 'evals/DS100-Evaluation-Suite-Plan.md');
const DEFAULT_OUTPUT_BASE = path.resolve(PROJECT_ROOT, 'eval/results');

const STATUS_VALUES = new Set(['pass', 'fail', 'unknown', 'error', 'skipped']);

const SMT_STRATEGIES = [
  {
    id: 'smt-z3-incremental-refutation',
    solver: 'z3',
    solvingStyle: 'incremental-refutation',
  },
  {
    id: 'smt-z3-incremental-model',
    solver: 'z3',
    solvingStyle: 'incremental-model-finding',
  },
  {
    id: 'smt-cvc5-incremental-refutation',
    solver: 'cvc5',
    solvingStyle: 'incremental-refutation',
  },
  {
    id: 'smt-cvc5-incremental-model',
    solver: 'cvc5',
    solvingStyle: 'incremental-model-finding',
  },
];

const INTUITION_STRATEGIES = [
  {
    id: 'no-intuition',
    usesVSARepresentation: false,
  },
  {
    id: 'vsa-intuition',
    usesVSARepresentation: true,
  },
];

const VSA_REPRESENTATIONS = [
  {
    id: 'vsa-hrr-cosine-topk',
    family: 'hrr',
    retrieval: 'cosine-topk',
  },
  {
    id: 'vsa-hdc-binary-hamming-topk',
    family: 'hdc-binary',
    retrieval: 'hamming-topk',
  },
];

const VSA_DISABLED = {
  id: 'vsa-disabled',
  family: 'none',
  retrieval: 'none',
};

function printUsage() {
  console.log(`HoloProof evaluation matrix runner

Usage:
  node eval/runEval.mjs [options]

Options:
  --mode <smoke|all>     Execution profile (default: smoke)
  --runner <command>     External runner command executed per case+combination
  --plan <path>          Case plan markdown path (default: evals/DS100-Evaluation-Suite-Plan.md)
  --output <dir>         Output directory (default: eval/results/<timestamp>)
  --max-cases <n>        Limit number of cases (useful for quick checks)
  --list-only            Print matrix and exit without execution
  --dry-run              Force dry-run mode (records skipped results)
  --help                 Show this help

Runner contract:
  The runner command receives context through env vars:
    HP_EVAL_CASE_ID
    HP_EVAL_COMBINATION_ID
    HP_EVAL_SMT_STRATEGY
    HP_EVAL_SOLVER
    HP_EVAL_INTUITION_STRATEGY
    HP_EVAL_VSA_REPRESENTATION
    HP_EVAL_LLM_PROFILE
    HP_EVAL_LLM_MODE
    HP_EVAL_LLM_MODEL

  If runner prints a JSON object on the last stdout line with { status, verdict?, elapsedMs? },
  it is used directly. Otherwise, exit code 0 maps to status=pass.
`);
}

function parseArgs(argv) {
  const args = {
    mode: 'smoke',
    runner: null,
    plan: DEFAULT_PLAN_PATH,
    output: null,
    maxCases: null,
    listOnly: false,
    dryRun: false,
    help: false,
  };

  for (let i = 0; i < argv.length; i += 1) {
    const token = argv[i];

    if (token === '--help') {
      args.help = true;
      continue;
    }
    if (token === '--list-only') {
      args.listOnly = true;
      continue;
    }
    if (token === '--dry-run') {
      args.dryRun = true;
      continue;
    }

    const [key, inlineValue] = token.includes('=') ? token.split(/=(.*)/, 2) : [token, null];

    const readValue = () => {
      if (inlineValue !== null) {
        return inlineValue;
      }
      i += 1;
      return argv[i] ?? null;
    };

    if (key === '--mode') {
      args.mode = readValue() ?? args.mode;
      continue;
    }
    if (key === '--runner') {
      args.runner = readValue();
      continue;
    }
    if (key === '--plan') {
      const value = readValue();
      if (value) {
        args.plan = path.resolve(PROJECT_ROOT, value);
      }
      continue;
    }
    if (key === '--output') {
      const value = readValue();
      if (value) {
        args.output = path.resolve(PROJECT_ROOT, value);
      }
      continue;
    }
    if (key === '--max-cases') {
      const value = Number(readValue());
      if (Number.isFinite(value) && value > 0) {
        args.maxCases = Math.floor(value);
      }
      continue;
    }

    throw new Error(`Unknown argument: ${token}`);
  }

  if (!['smoke', 'all'].includes(args.mode)) {
    throw new Error(`Invalid --mode value "${args.mode}". Use smoke or all.`);
  }

  return args;
}

function uniquePreserveOrder(values) {
  const seen = new Set();
  const out = [];
  for (const value of values) {
    if (seen.has(value)) {
      continue;
    }
    seen.add(value);
    out.push(value);
  }
  return out;
}

async function loadCaseIds(planPath) {
  const text = await fs.readFile(planPath, 'utf8');
  const matches = [...text.matchAll(/\bEV\d{3}\b/g)].map((match) => match[0]);
  const caseIds = uniquePreserveOrder(matches)
    .sort((left, right) => Number(left.slice(2)) - Number(right.slice(2)));
  if (!caseIds.length) {
    throw new Error(`No EVxxx case IDs found in plan file: ${planPath}`);
  }
  return caseIds;
}

function selectSmokeCases(allCaseIds) {
  const selected = allCaseIds.filter((caseId) => {
    const numeric = Number(caseId.slice(2));
    return Number.isFinite(numeric) && numeric % 10 === 1;
  });

  if (selected.length >= 10) {
    return selected.slice(0, 10);
  }

  return allCaseIds.slice(0, Math.min(10, allCaseIds.length));
}

function buildCombinationId(parts) {
  return [parts.smt.id, parts.intuition.id, parts.vsa.id, parts.llm.id].join('__');
}

function firstBySolver(solver) {
  return SMT_STRATEGIES.find((strategy) => strategy.solver === solver) || SMT_STRATEGIES[0];
}

async function discoverLLMProfiles() {
  const fallback = [
    {
      id: 'llm-fast-default',
      mode: 'fast',
      model: 'fast-unresolved',
      source: 'fallback',
    },
    {
      id: 'llm-deep-default',
      mode: 'deep',
      model: 'deep-unresolved',
      source: 'fallback',
    },
  ];

  try {
    const moduleUrl = new URL('../../AchillesAgentLib/utils/LLMClient.mjs', import.meta.url);
    const achilles = await import(moduleUrl.href);
    const strategy = achilles.defaultLLMInvokerStrategy;

    if (!strategy || typeof strategy.listAvailableModels !== 'function') {
      return fallback;
    }

    const available = strategy.listAvailableModels() || {};
    const fastModel = Array.isArray(available.fast) && available.fast.length
      ? available.fast[0]?.name || 'fast-unresolved'
      : 'fast-unresolved';

    const deepModel = Array.isArray(available.deep) && available.deep.length
      ? available.deep[0]?.name || 'deep-unresolved'
      : 'deep-unresolved';

    return [
      {
        id: 'llm-fast-default',
        mode: 'fast',
        model: fastModel,
        source: 'achilles',
      },
      {
        id: 'llm-deep-default',
        mode: 'deep',
        model: deepModel,
        source: 'achilles',
      },
    ];
  } catch {
    return fallback;
  }
}

function vsaRepresentationsFor(intuitionStrategy, mode) {
  if (!intuitionStrategy.usesVSARepresentation) {
    return [VSA_DISABLED];
  }

  if (mode === 'smoke') {
    return [VSA_REPRESENTATIONS[0]];
  }

  return VSA_REPRESENTATIONS;
}

function buildCombinations(mode, llmProfiles) {
  const smtList = mode === 'smoke'
    ? uniquePreserveOrder([firstBySolver('z3'), firstBySolver('cvc5')])
    : SMT_STRATEGIES;

  const combinations = [];

  for (const smt of smtList) {
    for (const intuition of INTUITION_STRATEGIES) {
      const vsaList = vsaRepresentationsFor(intuition, mode);
      for (const vsa of vsaList) {
        for (const llm of llmProfiles) {
          combinations.push({
            id: buildCombinationId({ smt, intuition, vsa, llm }),
            smt,
            intuition,
            vsa,
            llm,
          });
        }
      }
    }
  }

  return combinations;
}

function maybeParseRunnerJson(stdout) {
  const lines = stdout.split('\n').map((line) => line.trim()).filter(Boolean);

  for (let i = lines.length - 1; i >= 0; i -= 1) {
    const line = lines[i];
    try {
      const parsed = JSON.parse(line);
      if (parsed && typeof parsed === 'object') {
        const status = typeof parsed.status === 'string' ? parsed.status.toLowerCase() : null;
        if (status && STATUS_VALUES.has(status)) {
          return parsed;
        }
      }
    } catch {
      // Ignore non-JSON lines.
    }
  }

  return null;
}

function runRunnerCommand(command, env) {
  return new Promise((resolve) => {
    const startedAt = performance.now();
    const child = spawn(command, {
      cwd: PROJECT_ROOT,
      env,
      shell: true,
      stdio: ['ignore', 'pipe', 'pipe'],
    });

    let stdout = '';
    let stderr = '';

    child.stdout.on('data', (chunk) => {
      stdout += chunk.toString();
    });

    child.stderr.on('data', (chunk) => {
      stderr += chunk.toString();
    });

    child.on('close', (code) => {
      const elapsedMs = performance.now() - startedAt;
      resolve({ code, stdout, stderr, elapsedMs });
    });
  });
}

async function runOneCase({ caseId, combination, runnerCommand, dryRun }) {
  if (dryRun || !runnerCommand) {
    return {
      status: 'skipped',
      verdict: null,
      elapsedMs: 0,
      note: 'Dry run: no runner execution.',
      rawStdout: '',
      rawStderr: '',
    };
  }

  const env = {
    ...process.env,
    HP_EVAL_CASE_ID: caseId,
    HP_EVAL_COMBINATION_ID: combination.id,
    HP_EVAL_SMT_STRATEGY: combination.smt.id,
    HP_EVAL_SOLVER: combination.smt.solver,
    HP_EVAL_INTUITION_STRATEGY: combination.intuition.id,
    HP_EVAL_VSA_REPRESENTATION: combination.vsa.id,
    HP_EVAL_LLM_PROFILE: combination.llm.id,
    HP_EVAL_LLM_MODE: combination.llm.mode,
    HP_EVAL_LLM_MODEL: combination.llm.model,

    // Backward-compatible aliases
    HP_EVAL_VSA_STRATEGY: combination.vsa.id,
    HP_EVAL_INTUITION_IMPL: combination.intuition.id,
  };

  const execution = await runRunnerCommand(runnerCommand, env);

  const parsed = maybeParseRunnerJson(execution.stdout);
  if (parsed) {
    const status = String(parsed.status || '').toLowerCase();
    return {
      status: STATUS_VALUES.has(status) ? status : 'error',
      verdict: parsed.verdict ?? null,
      elapsedMs: Number.isFinite(parsed.elapsedMs) ? Number(parsed.elapsedMs) : execution.elapsedMs,
      note: parsed.note ?? null,
      rawStdout: execution.stdout,
      rawStderr: execution.stderr,
    };
  }

  if (execution.code === 0) {
    return {
      status: 'pass',
      verdict: null,
      elapsedMs: execution.elapsedMs,
      note: 'Runner exited with 0 and no JSON payload was provided.',
      rawStdout: execution.stdout,
      rawStderr: execution.stderr,
    };
  }

  return {
    status: 'error',
    verdict: null,
    elapsedMs: execution.elapsedMs,
    note: `Runner failed with exit code ${execution.code}.`,
    rawStdout: execution.stdout,
    rawStderr: execution.stderr,
  };
}

function summarizeByCombination(records, combinations) {
  const map = new Map();

  for (const combo of combinations) {
    map.set(combo.id, {
      combinationId: combo.id,
      strategy: combo,
      totalCases: 0,
      executedCases: 0,
      pass: 0,
      fail: 0,
      unknown: 0,
      error: 0,
      skipped: 0,
      totalElapsedMs: 0,
      avgElapsedMs: null,
      successRate: null,
      speedRatioVsFastest: null,
    });
  }

  for (const record of records) {
    const row = map.get(record.combinationId);
    if (!row) {
      continue;
    }

    row.totalCases += 1;
    row.totalElapsedMs += record.elapsedMs;

    const status = STATUS_VALUES.has(record.status) ? record.status : 'error';
    row[status] += 1;

    if (status !== 'skipped') {
      row.executedCases += 1;
    }
  }

  for (const row of map.values()) {
    if (row.executedCases > 0) {
      row.avgElapsedMs = row.totalElapsedMs / row.executedCases;
      row.successRate = row.pass / row.executedCases;
    }
  }

  const fastestAvg = [...map.values()]
    .filter((row) => Number.isFinite(row.avgElapsedMs) && row.avgElapsedMs > 0)
    .reduce((best, row) => Math.min(best, row.avgElapsedMs), Number.POSITIVE_INFINITY);

  if (Number.isFinite(fastestAvg)) {
    for (const row of map.values()) {
      if (Number.isFinite(row.avgElapsedMs) && row.avgElapsedMs > 0) {
        row.speedRatioVsFastest = row.avgElapsedMs / fastestAvg;
      }
    }
  }

  return [...map.values()];
}

function summarizeGlobal(records) {
  const global = {
    total: records.length,
    pass: 0,
    fail: 0,
    unknown: 0,
    error: 0,
    skipped: 0,
    totalElapsedMs: 0,
  };

  for (const record of records) {
    const status = STATUS_VALUES.has(record.status) ? record.status : 'error';
    global[status] += 1;
    global.totalElapsedMs += record.elapsedMs;
  }

  const executed = global.total - global.skipped;
  global.executed = executed;
  global.successRate = executed > 0 ? global.pass / executed : null;

  return global;
}

function csvEscape(value) {
  if (value === null || value === undefined) {
    return '';
  }
  const text = String(value);
  if (/[",\n]/.test(text)) {
    return `"${text.replaceAll('"', '""')}"`;
  }
  return text;
}

function buildSummaryCsv(summaryRows) {
  const headers = [
    'combinationId',
    'solver',
    'smtStrategy',
    'intuitionStrategy',
    'vsaRepresentation',
    'llmProfile',
    'llmMode',
    'llmModel',
    'totalCases',
    'executedCases',
    'pass',
    'fail',
    'unknown',
    'error',
    'skipped',
    'totalElapsedMs',
    'avgElapsedMs',
    'successRate',
    'speedRatioVsFastest',
  ];

  const lines = [headers.join(',')];

  for (const row of summaryRows) {
    const values = [
      row.combinationId,
      row.strategy.smt.solver,
      row.strategy.smt.id,
      row.strategy.intuition.id,
      row.strategy.vsa.id,
      row.strategy.llm.id,
      row.strategy.llm.mode,
      row.strategy.llm.model,
      row.totalCases,
      row.executedCases,
      row.pass,
      row.fail,
      row.unknown,
      row.error,
      row.skipped,
      row.totalElapsedMs.toFixed(3),
      row.avgElapsedMs !== null ? row.avgElapsedMs.toFixed(3) : '',
      row.successRate !== null ? row.successRate.toFixed(4) : '',
      row.speedRatioVsFastest !== null ? row.speedRatioVsFastest.toFixed(4) : '',
    ].map(csvEscape);

    lines.push(values.join(','));
  }

  return `${lines.join('\n')}\n`;
}

function timestampSlug() {
  return new Date().toISOString().replaceAll(':', '-').replaceAll('.', '-');
}

async function main() {
  const args = parseArgs(process.argv.slice(2));

  if (args.help) {
    printUsage();
    return;
  }

  const llmProfiles = await discoverLLMProfiles();
  const allCaseIds = await loadCaseIds(args.plan);

  const selectedCaseIds = args.mode === 'smoke'
    ? selectSmokeCases(allCaseIds)
    : allCaseIds.slice();

  const limitedCaseIds = args.maxCases
    ? selectedCaseIds.slice(0, args.maxCases)
    : selectedCaseIds;

  const combinations = buildCombinations(args.mode, llmProfiles);

  const dryRun = args.dryRun || !args.runner;
  const warnings = [];

  if (!args.runner) {
    warnings.push('No --runner command was provided; execution is dry-run and case results are marked as skipped.');
  }

  if (llmProfiles.some((profile) => profile.model.endsWith('-unresolved'))) {
    warnings.push('Achilles model discovery returned unresolved model names for fast/deep defaults.');
  }

  const outputDir = args.output || path.join(DEFAULT_OUTPUT_BASE, timestampSlug());

  console.log(`[runEval] Mode: ${args.mode}`);
  console.log(`[runEval] Cases: ${limitedCaseIds.length}`);
  console.log(`[runEval] Combinations: ${combinations.length}`);
  console.log(`[runEval] Runner: ${args.runner || 'none (dry-run)'}`);
  console.log(`[runEval] Output: ${outputDir}`);

  for (const warning of warnings) {
    console.warn(`[runEval] Warning: ${warning}`);
  }

  if (args.listOnly) {
    console.log('\n[runEval] Combination IDs:');
    for (const combination of combinations) {
      console.log(`- ${combination.id}`);
    }
    console.log('\n[runEval] Case IDs:');
    for (const caseId of limitedCaseIds) {
      console.log(`- ${caseId}`);
    }
    return;
  }

  await fs.mkdir(outputDir, { recursive: true });

  const records = [];

  for (let comboIndex = 0; comboIndex < combinations.length; comboIndex += 1) {
    const combination = combinations[comboIndex];
    console.log(`\n[runEval] Running combination ${comboIndex + 1}/${combinations.length}: ${combination.id}`);

    for (let caseIndex = 0; caseIndex < limitedCaseIds.length; caseIndex += 1) {
      const caseId = limitedCaseIds[caseIndex];
      const outcome = await runOneCase({
        caseId,
        combination,
        runnerCommand: args.runner,
        dryRun,
      });

      records.push({
        caseId,
        combinationId: combination.id,
        status: outcome.status,
        verdict: outcome.verdict,
        elapsedMs: outcome.elapsedMs,
        note: outcome.note,
        stderr: outcome.rawStderr,
      });

      const short = `${caseIndex + 1}/${limitedCaseIds.length}`;
      console.log(`[runEval]   ${short} ${caseId} -> ${outcome.status} (${outcome.elapsedMs.toFixed(2)} ms)`);
    }
  }

  const summaryRows = summarizeByCombination(records, combinations);
  const globalSummary = summarizeGlobal(records);

  const outputJson = {
    generatedAt: new Date().toISOString(),
    mode: args.mode,
    dryRun,
    runnerCommand: args.runner,
    planPath: args.plan,
    outputDir,
    warnings,
    matrix: {
      smtStrategies: SMT_STRATEGIES,
      intuitionStrategies: INTUITION_STRATEGIES,
      vsaRepresentations: VSA_REPRESENTATIONS,
      llmProfiles,
    },
    cases: limitedCaseIds,
    combinations,
    records,
    summary: {
      global: globalSummary,
      byCombination: summaryRows,
    },
  };

  const summaryCsv = buildSummaryCsv(summaryRows);

  await fs.writeFile(path.join(outputDir, 'results.json'), JSON.stringify(outputJson, null, 2), 'utf8');
  await fs.writeFile(path.join(outputDir, 'summary.csv'), summaryCsv, 'utf8');

  console.log('\n[runEval] Global summary:');
  console.log(`- Total runs: ${globalSummary.total}`);
  console.log(`- Executed: ${globalSummary.executed}`);
  console.log(`- Pass: ${globalSummary.pass}`);
  console.log(`- Fail: ${globalSummary.fail}`);
  console.log(`- Unknown: ${globalSummary.unknown}`);
  console.log(`- Error: ${globalSummary.error}`);
  console.log(`- Skipped: ${globalSummary.skipped}`);
  if (globalSummary.successRate !== null) {
    console.log(`- Success rate: ${(globalSummary.successRate * 100).toFixed(2)}%`);
  }
  console.log(`\n[runEval] Wrote ${path.join(outputDir, 'results.json')}`);
  console.log(`[runEval] Wrote ${path.join(outputDir, 'summary.csv')}`);
}

main().catch((error) => {
  console.error(`[runEval] Fatal: ${error.message}`);
  process.exitCode = 1;
});
