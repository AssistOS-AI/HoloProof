import { promises as fs } from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import {
  DEFAULT_LLM_CACHED_PROFILE,
  INTUITION_STRATEGIES,
  REGISTRY_CONTEXT_DISABLED,
  REGISTRY_CONTEXT_STRATEGIES,
  SMT_STRATEGIES,
  VSA_REPRESENTATIONS,
} from './constants.mjs';
import { buildRunEvalUsageText, createRunEvalDefaults, parseRunEvalArgs } from './args.mjs';
import { loadCaseIdsFromPlan, selectSmokeCases } from './cases.mjs';
import { buildCombinations } from './combinations.mjs';
import { discoverLLMProfiles } from './llmProfiles.mjs';
import { runOneCase } from './runner.mjs';
import { buildSummaryCsv, summarizeByCombination, summarizeGlobal } from './summary.mjs';
import { timestampSlug } from './utils.mjs';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);

export const DEFAULT_PROJECT_ROOT = path.resolve(__dirname, '../../..');

export async function runEvalCli(options = {}) {
  const projectRoot = options.projectRoot || DEFAULT_PROJECT_ROOT;
  const logger = options.logger || console;
  const argv = options.argv || [];
  const env = options.env || process.env;
  const defaults = createRunEvalDefaults(projectRoot);
  const args = parseRunEvalArgs(argv, { projectRoot, defaults });

  if (args.help) {
    logger.log(buildRunEvalUsageText());
    return { kind: 'help', exitCode: 0 };
  }

  const llmProfiles = args.useLLM
    ? await discoverLLMProfiles()
    : [DEFAULT_LLM_CACHED_PROFILE];
  const registryContextStrategies = args.useLLM
    ? REGISTRY_CONTEXT_STRATEGIES
    : [REGISTRY_CONTEXT_DISABLED];

  const allCaseIds = await loadCaseIdsFromPlan(args.plan);
  const selectedCaseIds = args.mode === 'smoke'
    ? selectSmokeCases(allCaseIds)
    : allCaseIds.slice();

  const limitedCaseIds = args.maxCases
    ? selectedCaseIds.slice(0, args.maxCases)
    : selectedCaseIds;

  const combinations = buildCombinations(args.mode, llmProfiles, {
    registryContextStrategies,
    registryContextDisabled: REGISTRY_CONTEXT_DISABLED,
  });

  const dryRun = args.dryRun || !args.runner;
  const warnings = [];

  if (!args.runner) {
    warnings.push('No --runner command was provided; execution is dry-run and case results are marked as skipped.');
  }

  if (args.useLLM && llmProfiles.some((profile) => profile.model.endsWith('-unresolved'))) {
    warnings.push('Achilles model discovery returned unresolved model names for fast/deep defaults.');
  }

  const outputDir = args.output || path.join(defaults.outputBase, timestampSlug(new Date()));

  logger.log(`[runEval] Mode: ${args.mode}`);
  logger.log(`[runEval] Cases: ${limitedCaseIds.length}`);
  logger.log(`[runEval] Combinations: ${combinations.length}`);
  logger.log(`[runEval] LLM mode: ${args.useLLM ? 'live-llm-generation' : 'cached-smt'}`);
  logger.log(`[runEval] SMT cache: ${args.smtCache}`);
  logger.log(`[runEval] Runner: ${args.runner || 'none (dry-run)'}`);
  logger.log(`[runEval] Output: ${outputDir}`);

  for (const warning of warnings) {
    logger.warn(`[runEval] Warning: ${warning}`);
  }

  if (args.listOnly) {
    logger.log('\n[runEval] Combination IDs:');
    for (const combination of combinations) {
      logger.log(`- ${combination.id}`);
    }
    logger.log('\n[runEval] Case IDs:');
    for (const caseId of limitedCaseIds) {
      logger.log(`- ${caseId}`);
    }
    return {
      kind: 'list-only',
      exitCode: 0,
      cases: limitedCaseIds,
      combinations,
    };
  }

  await fs.mkdir(outputDir, { recursive: true });

  const records = [];

  for (let comboIndex = 0; comboIndex < combinations.length; comboIndex += 1) {
    const combination = combinations[comboIndex];
    logger.log(`\n[runEval] Running combination ${comboIndex + 1}/${combinations.length}: ${combination.id}`);

    for (let caseIndex = 0; caseIndex < limitedCaseIds.length; caseIndex += 1) {
      const caseId = limitedCaseIds[caseIndex];
      const outcome = await runOneCase({
        caseId,
        combination,
        runnerCommand: args.runner,
        dryRun,
        useLLM: args.useLLM,
        smtCacheDir: args.smtCache,
        baseEnv: env,
        cwd: projectRoot,
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
      logger.log(`[runEval]   ${short} ${caseId} -> ${outcome.status} (${outcome.elapsedMs.toFixed(2)} ms)`);
    }
  }

  const summaryRows = summarizeByCombination(records, combinations);
  const globalSummary = summarizeGlobal(records);

  const outputJson = {
    generatedAt: new Date().toISOString(),
    mode: args.mode,
    llmInvocationMode: args.useLLM ? 'live-llm-generation' : 'cached-smt',
    smtCacheDir: args.smtCache,
    dryRun,
    runnerCommand: args.runner,
    planPath: args.plan,
    outputDir,
    warnings,
    matrix: {
      smtStrategies: SMT_STRATEGIES,
      intuitionStrategies: INTUITION_STRATEGIES,
      vsaRepresentations: VSA_REPRESENTATIONS,
      registryContextStrategies,
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

  logger.log('\n[runEval] Global summary:');
  logger.log(`- Total runs: ${globalSummary.total}`);
  logger.log(`- Executed: ${globalSummary.executed}`);
  logger.log(`- Pass: ${globalSummary.pass}`);
  logger.log(`- Fail: ${globalSummary.fail}`);
  logger.log(`- Unknown: ${globalSummary.unknown}`);
  logger.log(`- Error: ${globalSummary.error}`);
  logger.log(`- Skipped: ${globalSummary.skipped}`);
  if (globalSummary.successRate !== null) {
    logger.log(`- Success rate: ${(globalSummary.successRate * 100).toFixed(2)}%`);
  }
  logger.log(`\n[runEval] Wrote ${path.join(outputDir, 'results.json')}`);
  logger.log(`[runEval] Wrote ${path.join(outputDir, 'summary.csv')}`);

  return {
    kind: 'run',
    exitCode: 0,
    outputDir,
    summary: outputJson.summary,
  };
}
