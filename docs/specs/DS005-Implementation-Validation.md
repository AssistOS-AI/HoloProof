# DS005 - Implementation and Validation Plan

## Node.js MVP Profile

HoloProof targets Node.js ESM (`.mjs`) with `async/await` and low dependency weight. Z3 and CVC5 are integrated as external subprocesses speaking SMT-LIB2 through stdin/stdout. The VSA/HDC/HRR layer is implemented locally with deterministic hashing and typed arrays (`Float32Array`, `Int32Array`).

A practical project skeleton is:

```text
src/
  chat/
  reasoning/
  intuition/
  encoding/
  response/
  worlds/
  adapters/
    solver/
      z3Adapter.mjs
      cvc5Adapter.mjs
    llm/
      achillesLLMAgentAdapter.mjs
  observability/
  tests/
```

## Interface Normalization

Solver adapters must expose a normalized response envelope so upper layers remain backend-agnostic. At minimum, each call returns `verdict`, `elapsedMs`, and optional `model`, `unsatCore`, and backend diagnostics.

The LLM adapter must isolate Achilles-specific invocation details while preserving a clean contract for encoder/query/decoder modules.

## Observability and Audit Trail

Each query execution must persist a trace with world ID, snapshot ID, formal query, active fragment IDs, chosen strategy, budget values, elapsed timing, and solver artifacts. This trace is the foundation for debugging, governance, and reproducibility.

## Test Strategy

The MVP test suite should combine unit tests for adapters and integration tests for full query cycles on small synthetic knowledge packs. The expected assertions are deterministic verdicts, stable provenance mapping, and controlled behavior under ambiguity or conflict.

## Evaluation Orchestration Contract

Comparative evaluation must run across strategy combinations instead of one fixed pipeline. The orchestrator script is `eval/runEval.mjs`.

The script should support two execution profiles:

- `smoke`: quick validation with default strategy combinations.
- `all`: full Cartesian strategy sweep for comparative benchmarking.

At minimum, every evaluation run records:

- strategy tuple (SMT + VSA + Intuition implementation + LLM profile),
- pass/fail/unknown/error counts,
- elapsed timing and average per case,
- aggregate success rate,
- comparative speed ratio against the fastest combination in that run.

Results should be persisted under `eval/results/` in machine-readable format so trend analysis can be automated later.

## Controlled Risks

The dominant risk is semantic drift in NL-to-formal translation, not subprocess integration. Mitigation is procedural: proposal states, strict validation gates, clarification prompts for ambiguity, and explicit refusal to treat unvalidated LLM output as accepted knowledge.
