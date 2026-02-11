# Eval Runner

This directory contains orchestration utilities for strategy-combination benchmarking.

## Entry Point

- `eval/runEval.mjs`

Implementation note: `eval/runEval.mjs` is a thin CLI wrapper. Core evaluation logic is implemented in `src/sdk/eval/`.

## Quick Commands

Smoke matrix with default combinations (dry-run if no runner is provided):

```bash
node eval/runEval.mjs --mode smoke
```

Default plan source is `docs/specs/DS010-Evaluation-Suite-Plan.md`.

Default structured case source is `eval/cases/` (JSON files). If no structured files are found, runner falls back to case IDs extracted from plan markdown.

Smoke uses a deterministic stratified subset (20 cases, two per track).

Full matrix over all strategy combinations:

```bash
node eval/runEval.mjs --mode all
```

Run with an external case runner command:

```bash
node eval/runEval.mjs --mode smoke --runner "node src/eval/executeCase.mjs"
```

Run live LLM generation mode (instead of cached SMT mode):

```bash
node eval/runEval.mjs --mode smoke --llm --runner "node src/eval/executeCase.mjs"
```

Force case source directory explicitly:

```bash
node eval/runEval.mjs --mode smoke --cases-dir eval/cases
```

List combinations and cases without executing:

```bash
node eval/runEval.mjs --mode all --list-only
```

## Runner Environment Variables

If `--runner` is provided, each case execution receives:

- `HP_EVAL_CASE_ID`
- `HP_EVAL_COMBINATION_ID`
- `HP_EVAL_SMT_STRATEGY`
- `HP_EVAL_SOLVER`
- `HP_EVAL_INTUITION_STRATEGY`
- `HP_EVAL_VSA_REPRESENTATION`
- `HP_EVAL_REGISTRY_CONTEXT_STRATEGY`
- `HP_EVAL_LLM_PROFILE`
- `HP_EVAL_LLM_MODE`
- `HP_EVAL_LLM_MODEL`
- `HP_EVAL_LLM_INVOCATION_MODE`
- `HP_EVAL_USE_LLM`
- `HP_EVAL_SMT_CACHE_DIR`

Initial intuition strategy set:

- `no-intuition`
- `vsa-intuition`

Initial VSA/HDC baseline representations:

- `vsa-hrr-cosine-topk`
- `vsa-hdc-binary-hamming-topk`

Registry context strategies used in live LLM mode:

- `registry-context-usage-topk`
- `registry-context-vsa-similarity-topk`

## LLM Invocation and SMT Cache

Default mode is cached SMT execution (`cached-smt`) and should avoid live LLM calls for speed and determinism.

Use `--llm` to switch to live LLM generation mode when validating encoder/model behavior.

Optional cache directory override:

```bash
node eval/runEval.mjs --mode all --smt-cache eval/cache/smt
```

## Outputs

Results are written under `eval/results/<timestamp>/`:

- `results.json` full execution details
- `summary.csv` aggregate metrics by strategy combination
