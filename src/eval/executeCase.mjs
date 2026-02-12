#!/usr/bin/env node

import { createHash } from 'node:crypto';
import { promises as fs } from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { performance } from 'node:perf_hooks';
import {
  ChatOrchestrator,
  WorldManager,
  createAchillesLLMClient,
  createSolverSessionAdapter,
} from '../index.mjs';
import { DEMO_SCENARIOS } from '../../chat/demo-scenarios.mjs';
import { buildKnowledgePreview } from '../../chat/server/scenarioKnowledgeView.mjs';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);
const DEFAULT_PROJECT_ROOT = path.resolve(__dirname, '../..');

function stableSerialize(value) {
  if (value === null || value === undefined) {
    return 'null';
  }
  if (typeof value === 'string') {
    return JSON.stringify(value);
  }
  if (typeof value === 'number' || typeof value === 'boolean') {
    return JSON.stringify(value);
  }
  if (Array.isArray(value)) {
    return `[${value.map((item) => stableSerialize(item)).join(',')}]`;
  }
  if (typeof value === 'object') {
    const keys = Object.keys(value).sort();
    const entries = keys.map((key) => `${JSON.stringify(key)}:${stableSerialize(value[key])}`);
    return `{${entries.join(',')}}`;
  }
  return JSON.stringify(String(value));
}

function sha256(text) {
  return createHash('sha256').update(text).digest('hex');
}

function mapInterpretationToVerdict(interpretation, fallback = 'unknown') {
  const value = String(interpretation || '').trim().toLowerCase();
  if (value === 'entailed') {
    return 'entailed';
  }
  if (value === 'not-entailed' || value === 'satisfiable') {
    return 'not-entailed';
  }
  if (value === 'inconsistent') {
    return 'inconsistent';
  }
  if (value === 'consistent') {
    return 'consistent';
  }
  return String(fallback || 'unknown');
}

function registrySelectorFromEnv(rawId) {
  const value = String(rawId || '').toLowerCase();
  if (value.includes('vsa-similarity')) {
    return 'vsa-similarity-topk';
  }
  return 'usage-topk';
}

function modeFromEnv(rawMode) {
  const value = String(rawMode || '').toLowerCase();
  return value === 'deep' ? 'deep' : 'fast';
}

async function pathExists(targetPath) {
  try {
    await fs.access(targetPath);
    return true;
  } catch {
    return false;
  }
}

function createJsonFileCache(filePath) {
  let loaded = false;
  let data = {};

  async function ensureLoaded() {
    if (loaded) {
      return;
    }
    loaded = true;
    if (await pathExists(filePath)) {
      const raw = await fs.readFile(filePath, 'utf8');
      const parsed = JSON.parse(raw);
      if (parsed && typeof parsed === 'object' && !Array.isArray(parsed)) {
        data = parsed;
      }
    }
  }

  async function persist() {
    await fs.mkdir(path.dirname(filePath), { recursive: true });
    await fs.writeFile(filePath, JSON.stringify(data, null, 2), 'utf8');
  }

  return {
    async get(key) {
      await ensureLoaded();
      return data[key] ?? null;
    },

    async set(key, value) {
      await ensureLoaded();
      data[key] = value;
      await persist();
    },
  };
}

function createPromptCachedLLMClient(baseClient, promptCache, stats) {
  return {
    source: 'cached-llm',
    async complete(input = {}) {
      const payload = {
        mode: input.mode || 'fast',
        systemPrompt: String(input.systemPrompt || ''),
        userPrompt: String(input.userPrompt || ''),
      };
      const key = sha256(stableSerialize(payload));
      const hit = await promptCache.get(key);
      if (hit && typeof hit.text === 'string') {
        stats.promptCacheHits += 1;
        return {
          text: hit.text,
          raw: hit.raw || hit.text,
          cacheHit: true,
        };
      }

      if (!baseClient || typeof baseClient.complete !== 'function') {
        throw new Error('LLM cache miss and Achilles LLM client is unavailable.');
      }

      stats.promptCacheMisses += 1;
      const completion = await baseClient.complete(input);
      const text = String(completion?.text ?? completion ?? '').trim();
      await promptCache.set(key, {
        text,
        raw: completion?.raw || null,
        cachedAt: new Date().toISOString(),
      });
      return {
        text,
        raw: completion?.raw || completion,
        cacheHit: false,
      };
    },
  };
}

async function loadCaseDefinition(caseId, options = {}) {
  const casesDir = options.casesDir || path.join(options.projectRoot, 'eval/cases');
  const casePath = path.join(casesDir, `${caseId}.json`);
  const raw = await fs.readFile(casePath, 'utf8');
  const parsed = JSON.parse(raw);
  if (!parsed || typeof parsed !== 'object') {
    throw new Error(`Invalid case definition for ${caseId}.`);
  }
  return parsed;
}

function resolveCaseRuntime(caseDef) {
  if (caseDef.source === 'chat-demo' || typeof caseDef.scenarioId === 'string') {
    const scenario = DEMO_SCENARIOS.find((item) => item.id === caseDef.scenarioId);
    if (!scenario) {
      throw new Error(`Unknown chat demo scenario "${caseDef.scenarioId}".`);
    }
    const problemIndex = Number.isInteger(caseDef.problemIndex) ? caseDef.problemIndex : 0;
    const problem = scenario.problems?.[problemIndex];
    if (!problem) {
      throw new Error(`Scenario "${scenario.id}" does not have problem index ${problemIndex}.`);
    }
    const expectedVerdict = caseDef.expectedVerdict
      ? String(caseDef.expectedVerdict)
      : mapInterpretationToVerdict(problem.simulatedResult?.interpretation, 'unknown');

    return {
      title: caseDef.title || `${scenario.title} #${problemIndex + 1}`,
      knowledgeText: buildKnowledgePreview(scenario).join('\n'),
      queryText: caseDef.query || problem.prompt,
      expectedVerdict,
      scenario,
      problem,
    };
  }

  if (typeof caseDef.knowledgeText === 'string' && typeof caseDef.query === 'string') {
    return {
      title: caseDef.title || caseDef.caseId,
      knowledgeText: caseDef.knowledgeText,
      queryText: caseDef.query,
      expectedVerdict: String(caseDef.expectedVerdict || 'unknown'),
    };
  }

  return null;
}

function buildOutput(payload = {}) {
  return JSON.stringify({
    status: payload.status || 'error',
    verdict: payload.verdict ?? null,
    elapsedMs: Number.isFinite(payload.elapsedMs) ? Number(payload.elapsedMs) : 0,
    note: payload.note || null,
    cache: payload.cache || null,
  });
}

async function ingestScenarioDirect(worldManager, worldId, scenario, caseId) {
  if (!scenario || !Array.isArray(scenario.knowledge)) {
    return {
      ok: false,
      error: 'Scenario knowledge is unavailable for fallback ingest.',
    };
  }

  try {
    for (let i = 0; i < scenario.knowledge.length; i += 1) {
      const clone = JSON.parse(JSON.stringify(scenario.knowledge[i]));
      clone.worldId = worldId;
      clone.proposalId = `fp_${caseId.toLowerCase()}_fallback_${String(i + 1).padStart(2, '0')}`;
      worldManager.ingestProposal(worldId, clone);
      worldManager.promoteProposal(worldId, clone.proposalId);
    }
    return { ok: true };
  } catch (error) {
    return {
      ok: false,
      error: error instanceof Error ? error.message : String(error),
    };
  }
}

async function runEvalCase() {
  const startedAt = performance.now();
  const projectRoot = process.env.HP_EVAL_PROJECT_ROOT
    ? path.resolve(process.env.HP_EVAL_PROJECT_ROOT)
    : DEFAULT_PROJECT_ROOT;
  const caseId = String(process.env.HP_EVAL_CASE_ID || '').trim();
  const casesDir = process.env.HP_EVAL_CASES_DIR
    ? path.resolve(process.env.HP_EVAL_CASES_DIR)
    : path.join(projectRoot, 'eval/cases');

  if (!caseId) {
    throw new Error('HP_EVAL_CASE_ID is required.');
  }

  let caseDef = null;
  try {
    caseDef = await loadCaseDefinition(caseId, { projectRoot, casesDir });
  } catch (error) {
    if (error && error.code === 'ENOENT') {
      return {
        status: 'skipped',
        verdict: null,
        note: `No structured case file found for ${caseId} in ${casesDir}.`,
        elapsedMs: performance.now() - startedAt,
        cache: null,
      };
    }
    throw error;
  }
  const runtime = resolveCaseRuntime(caseDef);
  if (!runtime) {
    return {
      status: 'skipped',
      verdict: null,
      note: `Case "${caseId}" has no chat-demo or NL runtime definition yet.`,
      elapsedMs: performance.now() - startedAt,
      cache: null,
    };
  }

  const cacheBaseDir = process.env.HP_EVAL_SMT_CACHE_DIR
    ? path.resolve(process.env.HP_EVAL_SMT_CACHE_DIR)
    : path.join(projectRoot, 'eval/cache/smt');
  const promptCache = createJsonFileCache(path.join(cacheBaseDir, 'llm-prompt-cache.json'));
  const responseCache = createJsonFileCache(path.join(cacheBaseDir, 'llm-natural-response-cache.json'));
  const cacheStats = {
    promptCacheHits: 0,
    promptCacheMisses: 0,
  };

  const achillesClient = await createAchillesLLMClient({
    agentName: 'HoloProof-Eval',
  });
  const resilientBaseClient = {
    async complete(input = {}) {
      if (!achillesClient || typeof achillesClient.complete !== 'function') {
        return { text: 'not-json' };
      }
      try {
        return await achillesClient.complete(input);
      } catch {
        return { text: 'not-json' };
      }
    },
  };
  const llmClient = createPromptCachedLLMClient(resilientBaseClient, promptCache, cacheStats);

  const worldManager = new WorldManager();
  const solverAdapter = createSolverSessionAdapter();
  const worldId = `world_eval_${caseId.toLowerCase()}`;
  const orchestrator = new ChatOrchestrator({
    worldManager,
    solverAdapter,
    llmClient,
    defaultWorldId: worldId,
  });

  orchestrator.ensureWorld(worldId);
  worldManager.setStrategy(worldId, {
    smtStrategy: process.env.HP_EVAL_SMT_STRATEGY || undefined,
    intuitionStrategy: process.env.HP_EVAL_INTUITION_STRATEGY || undefined,
    vsaRepresentation: process.env.HP_EVAL_VSA_REPRESENTATION || undefined,
    llmProfile: process.env.HP_EVAL_LLM_PROFILE || undefined,
  });

  const llmMode = modeFromEnv(process.env.HP_EVAL_LLM_MODE);
  const registryContextStrategy = registrySelectorFromEnv(process.env.HP_EVAL_REGISTRY_CONTEXT_STRATEGY);

  const ingestResult = await orchestrator.processTurn({
    kind: 'ingest',
    worldId,
    proposalId: `fp_${caseId.toLowerCase()}_ingest`,
    sourceId: `eval:${caseId}:knowledge`,
    source: {
      sourceId: `eval:${caseId}:knowledge`,
      span: { start: 0, end: runtime.knowledgeText.length },
      createdAt: '2026-01-01T00:00:00.000Z',
    },
    text: runtime.knowledgeText,
    mode: llmMode,
    registryContextStrategy,
  });

  if (!ingestResult.ok) {
    const fallback = await ingestScenarioDirect(worldManager, worldId, runtime.scenario, caseId);
    if (!fallback.ok) {
      return {
        status: 'error',
        verdict: null,
        elapsedMs: performance.now() - startedAt,
        note: `Knowledge ingest failed for ${caseId}: ${ingestResult.errors?.[0] || fallback.error || 'unknown error'}`,
        cache: cacheStats,
      };
    }
  }

  const queryResult = await orchestrator.processTurn({
    kind: 'query',
    worldId,
    proposalId: `fp_${caseId.toLowerCase()}_query`,
    text: runtime.queryText,
    mode: llmMode,
    responseUseLLM: true,
    responseMode: 'fast',
    responseStyle: 'neutral',
    responseCache,
    registryContextStrategy,
  });

  if (!queryResult.ok) {
    return {
      status: 'error',
      verdict: null,
      elapsedMs: performance.now() - startedAt,
      note: `Query processing failed for ${caseId}: ${queryResult.errors?.[0] || 'unknown error'}`,
      cache: cacheStats,
    };
  }

  const verdict = String(queryResult.reasoning?.queryVerdict || queryResult.response?.queryVerdict || 'unknown');
  const expected = String(runtime.expectedVerdict || 'unknown');
  const status = expected === 'unknown'
    ? 'pass'
    : (verdict === expected ? 'pass' : 'fail');

  const answer = String(queryResult.response?.message || '').trim();
  const note = answer || `Case ${caseId} completed with verdict ${verdict}.`;

  return {
    status,
    verdict,
    elapsedMs: performance.now() - startedAt,
    note,
    cache: cacheStats,
  };
}

try {
  const result = await runEvalCase();
  console.log(buildOutput(result));
} catch (error) {
  console.log(buildOutput({
    status: 'error',
    verdict: null,
    note: error instanceof Error ? error.message : String(error),
    elapsedMs: 0,
  }));
}
