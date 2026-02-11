# DS009 - VSA Strategy: Binary HDC Hamming Ranking

## Purpose

This specification defines the second baseline representation strategy for `VSAIntuition`: binary HDC vectors with Hamming-distance ranking.

## Representation Model

Each fragment is encoded as a high-dimensional binary vector. Query encoding uses the same symbol dictionary and deterministic hashing to preserve comparability.

Composition and binding follow binary HDC operations (for example XOR-like composition and majority-based bundling where applicable).

Positional binding is mandatory. The strategy uses deterministic role hypervectors for predicate and argument positions:

- `role_pred`,
- `role_arg_0`, `role_arg_1`, ...

Canonical relation encoding uses role-aware XOR binding followed by bundle:

`termHV = bundle(xor(role_pred, predHV), xor(role_arg_0, arg0HV), xor(role_arg_1, arg1HV))`

where `bundle` is majority aggregation with deterministic tie-breaking.

This guarantees order sensitivity and avoids collapsing `likes(Alice, Bob)` into `likes(Bob, Alice)`.

## Candidate Selection

Ranking is based on normalized Hamming distance (or equivalent binary similarity). The selector returns top-k candidates with score metadata and fragment identifiers.

## Operational Notes

Binary HDC is useful as an implementation-friendly and robust baseline for noisy symbolic overlaps. It provides a distinct retrieval profile compared with dense HRR cosine ranking and is therefore mandatory in full matrix evaluation.

## Limits

Binary proximity remains heuristic evidence. Final correctness always comes from SMT reasoning on the selected formal fragment set.
