# DS005 - Implementation and Validation Plan

## Node.js Baseline Profile

HoloProof targets Node.js ESM (`.mjs`) with `async/await` and low dependency weight. Z3 and CVC5 are integrated as external subprocesses speaking SMT-LIB2 through stdin/stdout. The VSA/HDC/HRR layer is implemented locally with deterministic hashing and typed arrays (`Float32Array`, `Int32Array`).

A practical project skeleton is:

```text
src/
  sdk/
    eval/
    formalProposal.mjs
    symbolRegistry.mjs
    worldManager.mjs
    response/
    observability/
    solver/
    reasoning/
  chat/
  adapters/
    solver/
      z3Adapter.mjs
      cvc5Adapter.mjs
    llm/
      achillesLLMAgentAdapter.mjs
tests/
eval/
  runEval.mjs
```

`src/sdk/` is the single source of truth for core domain contracts. CLI/runtime layers (`eval/`, chat runtime) should be thin wrappers over SDK APIs.

## Interface Normalization

Solver adapters must expose a normalized response envelope so upper layers remain backend-agnostic. At minimum, each call returns `verdict`, `elapsedMs`, and optional `model`, `unsatCore`, and backend diagnostics.

The LLM adapter must isolate Achilles-specific invocation details while preserving a clean contract for encoder/query/decoder modules.

## SolverAdapter Session Lifecycle Contract

Incremental reasoning requires a stateful solver session, not one-shot subprocess calls. The adapter contract must expose explicit lifecycle operations:

```text
openSession(config) -> sessionId
push(sessionId)
pop(sessionId, levels=1)
assert(sessionId, assertions[])
checkSat(sessionId, options) -> { verdict, elapsedMs, stats }
getModel(sessionId) -> model | null
getUnsatCore(sessionId) -> core[] | null
reset(sessionId)
closeSession(sessionId)
```

`openSession` initializes logic, option flags, and timeout defaults. `push/pop` is mandatory for expansion loops and temporary assumptions. `getModel` and `getUnsatCore` are legal only after compatible verdicts (`sat` and `unsat`).

Session config includes resource budgets (`timeoutMs`, `maxMemoryMB`). If backend-native memory limits are unavailable, an OS-level guard is required.

Command execution must be serialized per session and aligned with deterministic synchronization markers (for example `(echo "HP_SYNC_<seq>")`) to avoid stdout/stderr desynchronization.

The parser contract must explicitly distinguish `check-sat` single-line verdicts from multi-line s-expression responses (`get-model`, `get-unsat-core`).

## Session Failure and Recovery

The adapter must classify failures into controlled outcomes:

- solver timeout: return `unknown` with timeout marker,
- recoverable command error: return `error` with command context and keep session open when safe,
- process crash or broken stream: mark session unhealthy, restart process, and replay stable accepted assertions from journaled state before continuing.

Recovery never replays transient branch assumptions blindly; only committed context up to last successful checkpoint is restored.

After recovery, adapter must emit a structured recovery event (`session-recovered`) so orchestrator re-dispatches pending query plans from top-level state instead of silently continuing mid-check.

Solver failures and degraded outcomes must be propagated as structured signals to response orchestration (not hidden behind generic text errors). This includes timeout markers, crash/recovery state, and parse/command failures.

## Persistence Strategy Contract

Persistence is strategy-based and must not be hard-wired to a single backend in core logic.

The world/fragment storage layer should be exposed through a `PersistenceAdapter` contract with at least one initial strategy: an intentionally unoptimized baseline implementation (for example copy-on-write JSON/file storage) used first for correctness and traceability.

Optimized strategies (for example relational or embedded databases) can be added later without changing orchestration or reasoning contracts.

## Observability and Audit Trail

Each query execution must persist a trace with world ID, snapshot ID, formal query, active fragment IDs, chosen strategy, budget values, elapsed timing, and solver artifacts. This trace is the foundation for debugging, governance, and reproducibility.

For incremental sessions, trace data must also include solver session events (`open`, `push`, `pop`, `assert`, `check`, `close`) with sequence numbers so the reasoning path can be reconstructed without ambiguity.

Trace persistence must enforce world-derived policy:

- sensitivity classification label,
- retention TTL,
- model/unsat-core redaction rules where required by policy.

Unsat core disclosure is policy-controlled. In restricted contexts, only redacted summaries or fragment IDs are returned.

## Test Strategy

The baseline test suite should combine unit tests for adapters and integration tests for full query cycles on small synthetic knowledge packs. The expected assertions are deterministic verdicts, stable provenance mapping, and controlled behavior under ambiguity or conflict.

## Evaluation Orchestration Contract

Comparative evaluation must run across strategy combinations instead of one fixed pipeline. The orchestrator script is `eval/runEval.mjs`.

The CLI script should import orchestration primitives from `src/sdk/eval/` rather than keeping duplicated matrix logic in the script body.

The script should support two execution profiles:

- `smoke`: quick validation with default strategy combinations.
- `all`: full Cartesian strategy sweep for comparative benchmarking.

At minimum, every evaluation run records:

- strategy tuple (SMT + Intuition strategy + VSA/HDC representation + registry context strategy + LLM profile),
- LLM invocation mode (`cached-smt` vs `live-llm-generation`),
- pass/fail/unknown/error counts,
- elapsed timing and average per case,
- aggregate success rate,
- comparative speed ratio against the fastest combination in that run.

Results should be persisted under `eval/results/` in machine-readable format so trend analysis can be automated later.

Deterministic replay contracts operate on stored `FormalProposal` IR plus solver artifacts. Replay must not re-invoke LLM generation.

## Controlled Risks

The dominant risk is semantic drift in NL-to-formal translation, not subprocess integration. Mitigation is procedural: proposal states, strict validation gates, clarification prompts for ambiguity, and explicit refusal to treat unvalidated LLM output as accepted knowledge.

When knowledge gaps are detected (missing symbols, missing supporting facts, failed solver checks), the system must surface them explicitly and route them through response decision policy:

- ask user for clarification/additional facts,
- or run bounded LLM autofill only when policy allows.

Any autofill output remains non-authoritative until promoted through standard world validation gates.
