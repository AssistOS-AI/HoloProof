# Eval Runner

This directory contains orchestration utilities for strategy-combination benchmarking.

## Entry Point

- `eval/runEval.mjs`

## Quick Commands

Smoke matrix with default combinations (dry-run if no runner is provided):

```bash
node eval/runEval.mjs --mode smoke
```

Full matrix over all strategy combinations:

```bash
node eval/runEval.mjs --mode all
```

Run with an external case runner command:

```bash
node eval/runEval.mjs --mode smoke --runner "node src/eval/executeCase.mjs"
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
- `HP_EVAL_LLM_PROFILE`
- `HP_EVAL_LLM_MODE`
- `HP_EVAL_LLM_MODEL`

Initial intuition strategy set:

- `no-intuition`
- `vsa-intuition`

Initial VSA/HDC baseline representations:

- `vsa-hrr-cosine-topk`
- `vsa-hdc-binary-hamming-topk`

## Outputs

Results are written under `eval/results/<timestamp>/`:

- `results.json` full execution details
- `summary.csv` aggregate metrics by strategy combination
