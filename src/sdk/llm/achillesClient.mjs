import path from 'node:path';
import { pathToFileURL } from 'node:url';

export const DEFAULT_ACHILLES_AGENT_MODULE_CANDIDATES = [
  'achillesAgentLib/LLMAgents/index.mjs',
  'AchillesAgentLib/LLMAgents/index.mjs',
  '../../../../AchillesAgentLib/LLMAgents/index.mjs',
];

function toModuleUrl(candidate) {
  if (candidate.startsWith('.')) {
    return new URL(candidate, import.meta.url).href;
  }
  return candidate;
}

function buildAbsoluteFallbackCandidates() {
  const cwd = process.cwd();
  return [
    path.resolve(cwd, '../AchillesAgentLib/LLMAgents/index.mjs'),
    path.resolve(cwd, 'AchillesAgentLib/LLMAgents/index.mjs'),
  ].map((filePath) => pathToFileURL(filePath).href);
}

export async function importAchillesLLMAgent(
  moduleCandidates = DEFAULT_ACHILLES_AGENT_MODULE_CANDIDATES,
  importFn = (modulePath) => import(modulePath),
) {
  const allCandidates = [...moduleCandidates, ...buildAbsoluteFallbackCandidates()];

  for (const candidate of allCandidates) {
    try {
      const moduleUrl = toModuleUrl(candidate);
      const mod = await importFn(moduleUrl);
      if (mod && typeof mod.LLMAgent === 'function') {
        return mod;
      }
    } catch {
      // Try next candidate.
    }
  }

  return null;
}

export async function createAchillesLLMClient(options = {}) {
  if (options.client && typeof options.client.complete === 'function') {
    return options.client;
  }

  const importer = options.importAchilles || importAchillesLLMAgent;
  const achilles = await importer(
    options.moduleCandidates || DEFAULT_ACHILLES_AGENT_MODULE_CANDIDATES,
    options.importFn,
  );

  if (!achilles?.LLMAgent) {
    return null;
  }

  const agentName = options.agentName || 'HoloProof-Encoder';
  const agent = new achilles.LLMAgent({ name: agentName });

  return {
    source: 'achilles',
    async complete(input = {}) {
      const mode = input.mode || 'fast';
      const systemPrompt = String(input.systemPrompt || '').trim();
      const userPrompt = String(input.userPrompt || '').trim();
      const history = [];

      if (systemPrompt) {
        history.push({ role: 'system', message: systemPrompt });
      }

      history.push({ role: 'user', message: userPrompt });

      const response = await agent.complete({
        mode,
        prompt: userPrompt,
        history,
      });

      if (typeof response === 'string') {
        return {
          text: response,
          raw: response,
        };
      }

      if (response && typeof response === 'object') {
        const text = String(response.text ?? response.message ?? response.output ?? '').trim();
        return {
          text,
          raw: response,
        };
      }

      return {
        text: '',
        raw: response,
      };
    },
  };
}
