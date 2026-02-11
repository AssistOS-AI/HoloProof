# HoloProof

HoloProof is a hybrid AI reasoning system that combines formal SMT solving with fast heuristic retrieval and controlled LLM-based translation.  
Its objective is simple: natural-language interaction with solver-backed answers that remain auditable.

The project is currently specification-first. The design set lives in `docs/specs/`, and implementation follows the contracts defined there.

## Short Vision

HoloProof turns natural language and source documents into formal constraints, verifies claims with solver backends such as Z3 or CVC5, and returns human-readable responses grounded in explicit evidence.

The solver is the logical authority. LLMs are used as controlled transducers for encoding and explanation, while intuition modules (VSA/HDC/HRR) are used for relevance filtering and speed.

## Installation

Detailed setup steps are available in:

- `docs/installation.html`

This guide covers environment prerequisites, solver installation, expected LLM integration with `../AchillesAgentLib`, and baseline project bootstrap commands.

## Usage Guide

Interactive usage and prompting guide:

- `docs/usage-guide.html`

The guide includes a two-tab demo (`Chat` and `Examples`) with 30 diverse examples and recommended prompt formulations for stronger NL-to-formal translation quality.

## Documentation Map

Main documentation index:

- `docs/index.html`

Design Specifications:

- `docs/specs/DS001-Vision.md`
- `docs/specs/DS002-Architecture.md`
- `docs/specs/DS003-Worlds-KB-Forking.md`
- `docs/specs/DS004-Reasoning-Intuition-LLM.md`
- `docs/specs/DS005-Implementation-Validation.md`
- `docs/specs/DS006-Chat-Examples-Experience.md`

Evaluation specification:

- `evals/DS100-Evaluation-Suite-Plan.md`

Evaluation runner:

- `eval/runEval.mjs`
- `eval/README.md`

Example commands:

```bash
node eval/runEval.mjs --mode smoke
node eval/runEval.mjs --mode all
```

## Language Policy

Interactive collaboration may be in Romanian or English.  
All persistent repository artifacts (code, comments, markdown, HTML docs, and specifications) are in English only.
