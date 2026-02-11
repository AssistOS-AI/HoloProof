# DS007 - Intuition Module

## Scope

This specification defines the Intuition module contract for HoloProof and the two initial strategies supported in MVP: `NoIntuition` and `VSAIntuition`.

## Module Role

The Intuition module is a pre-reasoning selector that proposes which knowledge fragments should be activated first for solver execution. It can improve speed and reduce solver load, but it does not decide truth.

## Strategy Set (Initial)

`NoIntuition` disables heuristic selection and passes a baseline selection policy to Reasoning (for example full active layer or deterministic baseline subset). This strategy is mandatory as a control baseline for evaluation.

`VSAIntuition` enables vector-symbolic ranking and proposes a top-k candidate set before formal solving. The strategy is compatible with multiple VSA/HDC representations.

## Interface Contract

The module exposes a stable strategy interface:

- `prepare(worldSnapshot)` for optional indexing/caching,
- `selectCandidates(queryContext, kbFragments, budget)` for candidate ranking,
- `explainSelection()` for traceable diagnostics.

When strategy is `NoIntuition`, diagnostics should explicitly report that heuristic ranking is disabled.

## Shared Positional Binding Requirement

All `VSAIntuition` representation strategies must preserve argument-order semantics through a shared positional-role contract. This prevents collisions such as treating `likes(Alice, Bob)` as equivalent to `likes(Bob, Alice)`.

Concrete binding operators are strategy-specific and are defined in DS008 and DS009, but both must encode predicate role and argument-position roles deterministically.

## Evaluation Requirement

All benchmark runs must include both strategies. Comparative reporting should always show delta versus `NoIntuition`, so speedups or regressions from `VSAIntuition` remain measurable and auditable.

## Related Strategy Specifications

Representation-level behavior for `VSAIntuition` is defined in:

- `docs/specs/DS008-VSA-HRR-Strategy.md`
- `docs/specs/DS009-HDC-Binary-Strategy.md`
