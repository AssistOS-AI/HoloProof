import path from 'node:path';

export function createRunEvalDefaults(projectRoot) {
  return {
    planPath: path.resolve(projectRoot, 'docs/specs/DS010-Evaluation-Suite-Plan.md'),
    casesDir: path.resolve(projectRoot, 'eval/cases'),
    outputBase: path.resolve(projectRoot, 'eval/results'),
    smtCacheDir: path.resolve(projectRoot, 'eval/cache/smt'),
  };
}

export function buildRunEvalUsageText() {
  return `HoloProof evaluation matrix runner

Usage:
  node eval/runEval.mjs [options]

Options:
  --mode <smoke|all>     Execution profile (default: smoke)
  --runner <command>     External runner command executed per case+combination
  --plan <path>          Case plan markdown path (default: docs/specs/DS010-Evaluation-Suite-Plan.md)
  --cases-dir <path>     Structured case directory (default: eval/cases, fallback to --plan)
  --output <dir>         Output directory (default: eval/results/<timestamp>)
  --smt-cache <dir>      SMT cache directory (default: eval/cache/smt)
  --llm                  Enable live LLM generation mode (default uses cached SMT artifacts)
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
    HP_EVAL_REGISTRY_CONTEXT_STRATEGY
    HP_EVAL_LLM_PROFILE
    HP_EVAL_LLM_MODE
    HP_EVAL_LLM_MODEL
    HP_EVAL_LLM_INVOCATION_MODE
    HP_EVAL_USE_LLM
    HP_EVAL_SMT_CACHE_DIR

  If runner prints a JSON object on the last stdout line with { status, verdict?, elapsedMs? },
  it is used directly. Otherwise, exit code 0 maps to status=pass.
`;
}

export function parseRunEvalArgs(argv, options = {}) {
  const projectRoot = options.projectRoot || process.cwd();
  const defaults = options.defaults || createRunEvalDefaults(projectRoot);

  const args = {
    mode: 'smoke',
    runner: null,
    plan: defaults.planPath,
    casesDir: defaults.casesDir,
    output: null,
    smtCache: defaults.smtCacheDir,
    useLLM: false,
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
    if (token === '--llm') {
      args.useLLM = true;
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
        args.plan = path.resolve(projectRoot, value);
      }
      continue;
    }
    if (key === '--cases-dir') {
      const value = readValue();
      if (value) {
        args.casesDir = path.resolve(projectRoot, value);
      }
      continue;
    }
    if (key === '--output') {
      const value = readValue();
      if (value) {
        args.output = path.resolve(projectRoot, value);
      }
      continue;
    }
    if (key === '--smt-cache') {
      const value = readValue();
      if (value) {
        args.smtCache = path.resolve(projectRoot, value);
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
