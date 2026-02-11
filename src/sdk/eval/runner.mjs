import { spawn } from 'node:child_process';
import { performance } from 'node:perf_hooks';
import { STATUS_VALUES } from './constants.mjs';

export function maybeParseRunnerJson(stdout) {
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

export function buildRunnerEnv({
  baseEnv,
  caseId,
  combination,
  useLLM,
  smtCacheDir,
}) {
  return {
    ...baseEnv,
    HP_EVAL_CASE_ID: caseId,
    HP_EVAL_COMBINATION_ID: combination.id,
    HP_EVAL_SMT_STRATEGY: combination.smt.id,
    HP_EVAL_SOLVER: combination.smt.solver,
    HP_EVAL_INTUITION_STRATEGY: combination.intuition.id,
    HP_EVAL_VSA_REPRESENTATION: combination.vsa.id,
    HP_EVAL_REGISTRY_CONTEXT_STRATEGY: combination.registryContext.id,
    HP_EVAL_LLM_PROFILE: combination.llm.id,
    HP_EVAL_LLM_MODE: combination.llm.mode,
    HP_EVAL_LLM_MODEL: combination.llm.model,
    HP_EVAL_LLM_INVOCATION_MODE: useLLM ? 'live-llm-generation' : 'cached-smt',
    HP_EVAL_USE_LLM: useLLM ? '1' : '0',
    HP_EVAL_SMT_CACHE_DIR: smtCacheDir,

    // Backward-compatible aliases
    HP_EVAL_VSA_STRATEGY: combination.vsa.id,
    HP_EVAL_INTUITION_IMPL: combination.intuition.id,
  };
}

export function runRunnerCommand(command, options = {}) {
  const cwd = options.cwd || process.cwd();
  const env = options.env || process.env;
  const now = options.now || (() => performance.now());
  const spawnFn = options.spawnFn || spawn;

  return new Promise((resolve) => {
    const startedAt = now();
    const child = spawnFn(command, {
      cwd,
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
      const elapsedMs = now() - startedAt;
      resolve({ code, stdout, stderr, elapsedMs });
    });
  });
}

export async function runOneCase({
  caseId,
  combination,
  runnerCommand,
  dryRun,
  useLLM,
  smtCacheDir,
  baseEnv,
  cwd,
}) {
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

  const env = buildRunnerEnv({
    baseEnv,
    caseId,
    combination,
    useLLM,
    smtCacheDir,
  });

  const execution = await runRunnerCommand(runnerCommand, { cwd, env });
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
