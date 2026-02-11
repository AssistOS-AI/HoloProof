import { DEFAULT_LLM_DISCOVERY_FALLBACK } from './constants.mjs';

export const DEFAULT_ACHILLES_MODULE_CANDIDATES = [
  'achillesAgentLib/utils/LLMClient.mjs',
  'AchillesAgentLib/utils/LLMClient.mjs',
  '../../AchillesAgentLib/utils/LLMClient.mjs',
];

export async function importAchillesLLMClient(
  moduleCandidates = DEFAULT_ACHILLES_MODULE_CANDIDATES,
  importFn = (modulePath) => import(modulePath),
) {
  for (const candidate of moduleCandidates) {
    try {
      if (candidate.startsWith('.')) {
        const moduleUrl = new URL(candidate, import.meta.url);
        return await importFn(moduleUrl.href);
      }
      return await importFn(candidate);
    } catch {
      // Try next candidate.
    }
  }

  return null;
}

export async function discoverLLMProfiles(options = {}) {
  const fallback = options.fallbackProfiles || DEFAULT_LLM_DISCOVERY_FALLBACK;
  const importer = options.importAchilles || importAchillesLLMClient;

  try {
    const achilles = await importer();
    if (!achilles) {
      return fallback;
    }

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
