# Evals

This directory contains evaluation planning and, later, executable evaluation cases for HoloProof.

Current entry point:

- `evals/DS010-Evaluation-Suite-Plan.md`

The plan defines 100 diverse examples across logical reasoning, constraints, ambiguity handling, world forking, and robustness behavior.

It also defines initial strategy-combination benchmarking around:

- Intuition strategies: `no-intuition`, `vsa-intuition`
- VSA/HDC representations: `vsa-hrr-cosine-topk`, `vsa-hdc-binary-hamming-topk`

Execution orchestration for strategy-combination benchmarking is in:

- `eval/runEval.mjs`
