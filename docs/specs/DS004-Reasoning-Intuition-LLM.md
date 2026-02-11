# DS004 - Reasoning, Intuition, and LLM Contracts

## Reasoning Modes

The reasoning module executes three primary verification modes in MVP form: entailment checking (typically via refuting negation), model finding for existential questions, and consistency validation for world health checks. Each mode runs under explicit budgets for timeout, active atom count, and expansion rounds.

Incremental solver usage is mandatory. The engine keeps a live context and uses `push/pop` to extend or narrow assumptions during iterative search.

## Intuition-to-Reasoning Loop

Intuition computes dense vector representations for knowledge fragments and for the current query using deterministic HRR/VSA-style operations. Similarity ranking proposes a compact candidate set that is small enough for fast formal evaluation.

If solver output is `unknown` or the budget is exceeded, the orchestrator expands the active set in controlled steps and retries. Intuition therefore acts as a relevance accelerator, never as a source of proof.

## Strategy Dimensions for Benchmarking

HoloProof must treat reasoning and retrieval behavior as configurable strategy families, not fixed implementations.

The evaluation matrix should vary:

- SMT strategy combinations (backend plus solving style), at minimum with both `z3` and `cvc5`.
- VSA ranking strategies (for example HRR cosine, binary HDC hamming, and hybrid reranking).
- Intuition implementation strategies (for example typed-array single-thread, typed-array worker-thread, and optional WASM acceleration).

These strategy dimensions are benchmarked jointly, because real performance depends on interaction effects between solver behavior and candidate-selection behavior.

## LLM as Controlled Transducer

LLMs are responsible for structured transformations, not logical authority. `LLMEncoder` and `QueryEncoder` should emit structured JSON first, then generate SMT-LIB2 only after local schema validation.

`ResponseDecoder` receives only approved evidence: solver verdicts, optional model/core artifacts, and the final active formal set. Every explanatory claim in the final answer must map back to that evidence.

## Achilles AgentLLM Integration

Where LLM strategies are needed, HoloProof uses the parent-folder API from `AchillesAgentLib` instead of creating a custom provider stack from scratch. This enables multi-provider and multi-model routing with existing support for `fast` and `deep` modes.

```js
import { LLMAgent } from '../AchillesAgentLib/LLMAgents/index.mjs';

const encoderAgent = new LLMAgent({ name: 'HoloProof-Encoder' });

const structured = await encoderAgent.complete({
  mode: 'fast',
  prompt: 'Return strict JSON with symbols, assumptions, and ambiguities.',
  history: [{ role: 'user', message: userText }],
});
```

The same abstraction can be reused for multiple LLM strategies, including fallback chains, without changing reasoning-core logic.

For evaluation defaults, fast mode should pick the first configured fast model from Achilles model discovery, and comparison runs should also include the first configured deep model.
