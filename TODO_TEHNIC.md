# Technical TODO

This file tracks unresolved technical work migrated from previous external review notes.

## Priority A: End-to-End Runtime Completion

1. Implement `LLMEncoder` and `QueryEncoder` with AchillesAgentLib integration:
   - consume registry context strategies (`usage-topk`, `vsa-similarity-topk`),
   - emit strict `FormalProposal` JSON IR,
   - validate proposals before promotion.
2. Implement full chat orchestrator state machine:
   - flow `user -> encoder -> intuition -> reasoning -> response`,
   - world/snapshot/fork-aware execution,
   - explicit recovery path when solver emits `session-recovered`.
3. Complete `ResponseDecoder` natural-language generation path:
   - structured, anchor-backed explanation generation,
   - strict filtering of unanchored claims,
   - clarification-first behavior on KB gaps unless bounded LLM autofill is enabled.

## Priority B: Knowledge Selection and Reasoning Quality

1. Implement standalone Intuition module contract from DS007:
   - `prepare(worldSnapshot)`,
   - `selectCandidates(queryContext, kbFragments, budget)`,
   - `explainSelection()`.
2. Implement both VSA/HDC strategy families required by DS008 and DS009 on fragment-level retrieval:
   - HRR/cosine strategy,
   - binary HDC/hamming strategy,
   - deterministic positional-role binding.
3. Integrate intuition ranking directly into reasoning rounds (instead of external ranked IDs only).

## Priority C: Storage, Eval Data, and Operations

1. Add persistence adapter strategy (initial correctness-first unoptimized strategy).
2. Introduce structured evaluation case files (machine-readable case payloads, not only markdown IDs).
3. Add pre-flight complexity guard before solver execution (term/quantifier complexity estimate).
4. Add world cleanup API (`deleteWorld`) and lifecycle management for long-running processes.

## Priority D: Validation and Security Hardening

1. Make `WorldManager` promotion solver sanity check asynchronous with real adapter path.
2. Add prompt/input sanitization policy for user-provided textual metadata before LLM prompt assembly.
3. Extend trace/access governance beyond redaction (access-control integration for sensitive worlds).

## Completed Since Review (for context)

1. Deterministic SMT emitter and script generation were implemented.
2. Solver session lifecycle adapter was implemented (`open/push/pop/assert/checkSat/getModel/getUnsatCore/reset/close`) with recovery signaling.
3. FormalProposal now requires `logic` and supports `ite`/`distinct`.
4. Reserved prefix enforcement is active in validation/emission.
5. Query execution pipeline with KB-gap detection and response decision policy is implemented and unit-tested.
