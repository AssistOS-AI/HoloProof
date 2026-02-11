export const STATUS_VALUES = new Set(['pass', 'fail', 'unknown', 'error', 'skipped']);

export const SMT_STRATEGIES = [
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

export const INTUITION_STRATEGIES = [
  {
    id: 'no-intuition',
    usesVSARepresentation: false,
  },
  {
    id: 'vsa-intuition',
    usesVSARepresentation: true,
  },
];

export const VSA_REPRESENTATIONS = [
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

export const VSA_DISABLED = {
  id: 'vsa-disabled',
  family: 'none',
  retrieval: 'none',
};

export const REGISTRY_CONTEXT_STRATEGIES = [
  {
    id: 'registry-context-usage-topk',
    selector: 'usage-topk',
  },
  {
    id: 'registry-context-vsa-similarity-topk',
    selector: 'vsa-similarity-topk',
  },
];

export const REGISTRY_CONTEXT_DISABLED = {
  id: 'registry-context-disabled',
  selector: 'disabled',
};

export const SMOKE_CASE_IDS = [
  'EV001', 'EV005',
  'EV011', 'EV017',
  'EV021', 'EV024',
  'EV031', 'EV034',
  'EV041', 'EV046',
  'EV051', 'EV055',
  'EV061', 'EV066',
  'EV071', 'EV079',
  'EV081', 'EV084',
  'EV091', 'EV098',
];

export const DEFAULT_LLM_CACHED_PROFILE = {
  id: 'llm-cached',
  mode: 'none',
  model: 'cached-smt',
  source: 'cache',
};

export const DEFAULT_LLM_DISCOVERY_FALLBACK = [
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
