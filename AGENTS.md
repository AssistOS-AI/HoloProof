# AGENTS.md

## Project Name

HoloProof.

## Language Policy

Interactive collaboration can be in Romanian or English.

All persistent project artifacts must be in English only. This rule applies to source code, code comments, Markdown documentation, HTML documentation, design specifications, and any user-facing static content stored in the repository.

## Specification Map

The project specification map is organized under `docs/specs/` and currently includes:

- `docs/specs/DS001-Vision.md`
- `docs/specs/DS002-Architecture.md`
- `docs/specs/DS003-Worlds-KB-Forking.md`
- `docs/specs/DS004-Reasoning-Intuition-LLM.md`
- `docs/specs/DS005-Implementation-Validation.md`
- `docs/specs/DS006-Chat-Examples-Experience.md`
- `docs/specs/DS007-Intuition-Module.md`
- `docs/specs/DS008-VSA-HRR-Strategy.md`
- `docs/specs/DS009-HDC-Binary-Strategy.md`
- `docs/specs/DS010-Evaluation-Suite-Plan.md`
- `eval/runEval.mjs`

Documentation entry points:

- `docs/index.html` is the main specification index.
- `docs/loader.html` loads and renders `.md` files for fast browser viewing.
- `docs/installation.html` describes installation prerequisites and local setup flow.
- `docs/usage-guide.html` provides usage guidance and an interactive chat/examples demo.
- `eval/README.md` describes evaluation runner usage and output artifacts.

## Strategy and Integration Rules

HoloProof is strategy-oriented and should support multiple interchangeable backends where possible.

Core implementation lives in `src/` as a mini SDK. Runtime entry points (evaluation CLI and future chat runtime) must consume SDK exports instead of re-implementing core domain logic inline.

For formal reasoning, keep a common adapter interface and allow at least `z3` and `cvc5` implementations.

For LLM functionality, reuse the API from the parent folder `../AchillesAgentLib` (not custom ad-hoc provider calls in core modules). The expected integration style is through the `LLMAgent` abstraction and its existing fast/deep model-routing support.

Achilles integration should prefer package/module resolution when available and keep `../AchillesAgentLib` as workspace fallback.

Persistence must be strategy-based. The first persistence strategy is intentionally unoptimized and correctness-first.

Evaluation runs must benchmark strategy combinations across SMT, Intuition strategy, and VSA/HDC representation dimensions, and include both Achilles `fast-default` and `deep-default` LLM profiles when available.

For live LLM generation runs, evaluation also benchmarks registry-context strategies for encoder prompts: `registry-context-usage-topk` and `registry-context-vsa-similarity-topk`.

Default evaluation mode is cached SMT (no live LLM calls during case execution). Live LLM generation is enabled explicitly (for example with `--llm`) when testing encoder/model behavior.

The evaluation CLI entry point remains `eval/runEval.mjs`, but orchestration logic belongs to `src/sdk/eval/` and is imported by the CLI wrapper.

Initial Intuition strategy baseline:

- `no-intuition`
- `vsa-intuition`

Initial VSA/HDC representation baseline for `vsa-intuition`:

- `vsa-hrr-cosine-topk`
- `vsa-hdc-binary-hamming-topk`
