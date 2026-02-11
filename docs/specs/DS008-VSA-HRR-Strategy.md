# DS008 - VSA Strategy: HRR Cosine Ranking

## Purpose

This specification defines the first VSA representation strategy for `VSAIntuition`: HRR-style dense vectors with cosine similarity ranking.

## Representation Model

Each knowledge fragment is encoded as a dense hypervector. Query vectors are generated with the same deterministic encoding rules so similarity is comparable in one vector space.

Binding and composition follow HRR-compatible operations, while fragment vectors are normalized to stabilize ranking behavior.

Positional binding is mandatory. The strategy must use fixed role vectors per slot:

- predicate role vector (`role_pred`),
- argument role vectors (`role_arg_0`, `role_arg_1`, ...).

For relation terms, encoding uses role-aware composition so argument order is preserved. A canonical term encoding example is:

`termVec = bind(role_pred, predVec) + bind(role_arg_0, arg0Vec) + bind(role_arg_1, arg1Vec)`

where `bind` is circular convolution (HRR-compatible) and `+` is superposition.

This makes `likes(Alice, Bob)` and `likes(Bob, Alice)` produce distinct vectors under the same vocabulary and seed.

## Candidate Selection

Given a query vector and indexed fragment vectors, the strategy computes cosine similarity and returns a sorted top-k list under current query budget.

The output includes score values and fragment identifiers to support reproducible diagnostics.

## Operational Notes

HRR cosine ranking is expected to provide smooth relevance gradients and good recall for semantically close fragments. It is the default representation in smoke-profile evaluation because it offers a stable baseline for `VSAIntuition`.

## Limits

This strategy remains heuristic. High similarity does not imply logical entailment; solver validation is still mandatory before any answer claim.
