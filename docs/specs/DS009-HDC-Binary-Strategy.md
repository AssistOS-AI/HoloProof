# DS009 - VSA Strategy: Binary HDC Hamming Ranking

## Purpose

This specification defines the second baseline representation strategy for `VSAIntuition`: binary HDC vectors with Hamming-distance ranking.

## Representation Model

Each fragment is encoded as a high-dimensional binary vector. Query encoding uses the same symbol dictionary and deterministic hashing to preserve comparability.

Composition and binding follow binary HDC operations (for example XOR-like composition and majority-based bundling where applicable).

## Candidate Selection

Ranking is based on normalized Hamming distance (or equivalent binary similarity). The selector returns top-k candidates with score metadata and fragment identifiers.

## Operational Notes

Binary HDC is useful as an implementation-friendly and robust baseline for noisy symbolic overlaps. It provides a distinct retrieval profile compared with dense HRR cosine ranking and is therefore mandatory in full matrix evaluation.

## Limits

Binary proximity remains heuristic evidence. Final correctness always comes from SMT reasoning on the selected formal fragment set.
