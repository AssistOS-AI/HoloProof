# DS004 - Reasoning, Intuition, and LLM Contracts

## Reasoning Modes

The reasoning module executes three primary verification modes in MVP form: entailment checking (typically via refuting negation), model finding for existential questions, and consistency validation for world health checks. Each mode runs under explicit budgets for timeout, active atom count, and expansion rounds.

Incremental solver usage is mandatory. The engine keeps a live context and uses `push/pop` to extend or narrow assumptions during iterative search.

## Intuition-to-Reasoning Loop

Intuition computes dense vector representations for knowledge fragments and for the current query using deterministic HRR/VSA-style operations. Similarity ranking proposes a compact candidate set that is small enough for fast formal evaluation.

If solver output is `unknown` or the budget is exceeded, the orchestrator expands the active set in controlled steps and retries. Intuition therefore acts as a relevance accelerator, never as a source of proof.

Expansion loops must terminate with explicit controls: maximum expansion rounds, deterministic expansion step size, and stagnation stop conditions.

## Strategy Dimensions for Benchmarking

HoloProof must treat reasoning and retrieval behavior as configurable strategy families, not fixed implementations.

The evaluation matrix should vary:

- SMT strategy combinations (backend plus solving style), at minimum with both `z3` and `cvc5`.
- Intuition strategy mode: `NoIntuition` and `VSAIntuition`.
- VSA/HDC representation strategy used by `VSAIntuition`: initial baseline set is HRR cosine ranking and Binary HDC Hamming ranking.

These strategy dimensions are benchmarked jointly, because real performance depends on interaction effects between solver behavior and candidate-selection behavior.

Detailed Intuition strategy definitions are specified in `docs/specs/DS007-Intuition-Module.md`, `docs/specs/DS008-VSA-HRR-Strategy.md`, and `docs/specs/DS009-HDC-Binary-Strategy.md`.

## LLM as Controlled Transducer

LLMs are responsible for structured transformations, not logical authority. `LLMEncoder` and `QueryEncoder` should emit structured JSON first, then generate SMT-LIB2 only after local schema validation.

`ResponseDecoder` receives only approved evidence: solver verdicts, optional model/core artifacts, and the final active formal set. Every explanatory claim in the final answer must map back to that evidence.

Prompt contract for encoding must explicitly require symbol reuse and synonym avoidance:

- reuse existing registry symbols when conceptually equivalent,
- do not invent synonymous predicates/functions when an existing symbol fits,
- prefer registry aliases for sort reuse.

## FormalProposal JSON IR (v1)

The contract between `LLMEncoder`, local validators, and SMT emission is `FormalProposal`. This schema is mandatory; free-form SMT text from LLM output is not accepted as authoritative input.

Minimal shape:

```json
{
  "schemaVersion": "holoproof.formal-proposal.v1",
  "proposalId": "fp_000123",
  "worldId": "world_main",
  "source": {
    "sourceId": "doc_contract_12",
    "span": { "start": 120, "end": 264 },
    "createdAt": "2026-02-11T12:00:00Z"
  },
  "declarations": [
    { "kind": "sort", "name": "Person" },
    { "kind": "predicate", "name": "eligible", "argSorts": ["Person"], "resultSort": "Bool" }
  ],
  "assertions": [
    {
      "assertionId": "ax_1",
      "role": "axiom",
      "expr": {
        "op": "forall",
        "vars": [{ "name": "x", "sort": "Person" }],
        "body": {
          "op": "=>",
          "args": [
            { "op": "call", "symbol": "student", "args": [{ "op": "var", "name": "x" }] },
            { "op": "call", "symbol": "eligible", "args": [{ "op": "var", "name": "x" }] }
          ]
        }
      }
    }
  ],
  "queryPlan": {
    "verificationMode": "entailment",
    "goal": { "op": "call", "symbol": "eligible", "args": [{ "op": "const", "name": "Ana" }] }
  },
  "ambiguities": [],
  "tags": ["policy", "eligibility"]
}
```

Expression IR is intentionally compact and deterministic. MVP operators are sufficient for practical coverage: `const`, `var`, `call`, `not`, `and`, `or`, `=>`, `=`, arithmetic comparators, and quantifiers (`forall`, `exists`).

Identifier grammar is strict: `^[A-Za-z_][A-Za-z0-9_]*$`. Non-matching names are invalid at schema gate.

Reserved solver-command identifiers are blocked in user-space symbol names (for example `exit`, `assert`, `push`, `pop`, `set_option`, `declare_fun`).

## FormalProposal Validation Gates

Validation is deterministic and runs before solver interaction:

- schema gate: required fields, operator whitelist, and type-safe expression nodes,
- registry gate: declaration and usage compatibility with current world symbol registry,
- emission gate: deterministic SMT-LIB2 generation from IR and safe-command filtering.

A proposal that fails any gate remains `proposed` or becomes `contested` and cannot be auto-promoted into accepted knowledge.

## Deterministic Emission Rules

To keep reproducibility and cache hits stable, SMT generation from `FormalProposal` must follow fixed ordering:

- declarations sorted by `kind` then `name`,
- assertions emitted in array order with stable IDs,
- reserved symbol prefixes blocked (`hp_internal_`, solver meta symbols),
- same `FormalProposal` payload always yields byte-identical SMT output.

## Registry Context Budget for LLM

Large registries must be filtered before LLM encoding prompts. Context selection should prioritize high-usage and query-relevant symbols under a bounded size budget (for example top-k symbols plus aliases), while preserving deterministic selection rules.

## ResponseDecoder Evidence Anchoring

Response generation must use explicit claim anchors (fragment IDs, model keys, unsat-core IDs, verdict references). Claims without valid anchors are rejected or stripped before response emission.

Unknown verdict explanations must use uncertainty language and avoid definitive claims beyond approved evidence.

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

Integration policy should prefer Node module resolution (package import) when available, and use local path fallback (`../AchillesAgentLib`) in workspace setups. This keeps local development practical without turning relative paths into a hard deployment requirement.
