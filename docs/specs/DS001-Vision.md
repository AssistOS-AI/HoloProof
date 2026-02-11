# DS001 - Vision

HoloProof is a hybrid reasoning assistant that combines formal SMT solving with fast heuristic retrieval and controlled LLM transformations. The system is designed for people who want natural-language interaction without giving up verifiable logic.

## Purpose

HoloProof turns text questions and ingested documents into formal constraints, evaluates them with a solver, and returns human-readable answers tied to explicit evidence. The practical goal is to make knowledge-intensive reasoning usable in daily workflows while preserving auditability.

## Core Promise

The solver is the authority for truth inside the formalized world. LLMs are used for translation and explanation, not for final logical guarantees. The intuition layer (VSA/HDC/HRR) accelerates retrieval and context selection, but proof obligations always return to the solver.

## MVP Boundaries

The first implementation focuses on five capabilities: document ingestion, proposal-to-formalization flow, solver-backed querying, world-based session isolation, and traceable response generation. The MVP does not attempt perfect open-domain understanding; ambiguous content is surfaced for clarification instead of being silently guessed.

## Success Criteria

A successful query in HoloProof must provide a clear verdict (`sat`, `unsat`, or `unknown`), a precise mapping to active axioms and source fragments, and a readable natural-language explanation that stays aligned with solver artifacts.
