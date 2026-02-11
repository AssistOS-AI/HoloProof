# DS010 - Evaluation Suite Plan (100 Diverse Examples)

## Purpose

This design specification defines the first evaluation suite for HoloProof under `docs/specs/`. The objective is to demonstrate capability breadth and comparative runtime behavior across strategy combinations: SMT solving strategy, Intuition strategy, VSA/HDC representation strategy, and controlled LLM profile testing.

## Suite Structure

The suite contains 100 examples grouped into 10 tracks with 10 examples per track. Each track targets a different capability axis.

Track distribution:

- `T1` Logical entailment and contradiction (`EV001-EV010`)
- `T2` Arithmetic and bounded optimization-style constraints (`EV011-EV020`)
- `T3` Temporal and ordering constraints (`EV021-EV030`)
- `T4` Graph and reachability reasoning (`EV031-EV040`)
- `T5` Planning and resource feasibility (`EV041-EV050`)
- `T6` Policy, authorization, and compliance (`EV051-EV060`)
- `T7` Knowledge ingestion and provenance (`EV061-EV070`)
- `T8` Ambiguity and clarification loops (`EV071-EV080`)
- `T9` Worlds, snapshots, and fork comparison (`EV081-EV090`)
- `T10` Unknown handling, robustness, and stress budgets (`EV091-EV100`)

## Strategy Matrix Dimensions

The evaluation runner benchmarks combinations, not single strategies.

Strategy families for matrix generation:

- SMT strategy: backend + solving style, minimum `z3` and `cvc5`.
- Intuition strategy: `NoIntuition` and `VSAIntuition`.
- VSA/HDC representation strategy used when intuition is enabled: HRR cosine ranking and Binary HDC Hamming ranking.
- LLM profile factor (only when live LLM generation is enabled): first configured Achilles fast model and first configured Achilles deep model.

LLM selection rule for live-generation runs:

- `fast-default`: first configured model in Achilles fast list.
- `deep-default`: first configured model in Achilles deep list.

## Combination Profiles

`smoke` profile is a deterministic stratified subset intended for local checks and CI preflight. It must include both `NoIntuition` and `VSAIntuition`.

The baseline smoke subset is 20 cases (two per track) to avoid coverage bias toward only the first case in each track:

- EV001, EV005
- EV011, EV017
- EV021, EV024
- EV031, EV034
- EV041, EV046
- EV051, EV055
- EV061, EV066
- EV071, EV079
- EV081, EV084
- EV091, EV098

`all` profile is a full sweep over all configured strategy families, including both baseline VSA/HDC representations for `VSAIntuition`. This is used for comparative speed analysis and regression trend tracking.

## SMT Cache and LLM Invocation Policy

Default evaluation mode must not invoke LLMs for every case. Instead, it uses pre-generated SMT artifacts from a cache to keep runs fast and reproducible.

Live LLM generation is enabled explicitly (for example with `--llm`) to test encoder behavior and model-dependent quality.

This yields two execution modes:

- `cached-smt` (default): no live LLM calls during case execution.
- `live-llm-generation` (opt-in): LLM calls enabled for generation/translation testing.

Cache location should be configurable (for example with `--smt-cache`) to support CI/local path differences.

## Case Catalog

### T1: Logical Entailment and Contradiction

EV001 Syllogism with one universal rule and one instance.
EV002 Two-hop implication chain over class hierarchy.
EV003 Contradictory unary predicates on same entity.
EV004 Existential witness required for negated universal claim.
EV005 Multi-premise conjunction required for entailment.
EV006 Entailment fails due to missing premise.
EV007 Closed-world assumption conflict test.
EV008 Symmetry rule implication on relation pairs.
EV009 Transitivity over partial relation graph.
EV010 Unsat core extraction on three conflicting axioms.

### T2: Arithmetic and Constraint Solving

EV011 Linear budget under-cap validation.
EV012 Linear budget over-cap conflict detection.
EV013 Integer domain feasibility with lower and upper bounds.
EV014 Difference constraints between three variables.
EV015 Ratio threshold compliance check.
EV016 Piecewise rule activation by numeric threshold.
EV017 Counterexample search for invalid inequality claim.
EV018 Capacity balancing across two bins.
EV019 Minimum required value under dependent constraints.
EV020 Model extraction for satisfying assignment.

### T3: Temporal and Ordering Constraints

EV021 Single precedence constraint violation.
EV022 Multi-step precedence chain validation.
EV023 Interval overlap detection.
EV024 Non-overlap schedule feasibility.
EV025 Minimum gap constraint between events.
EV026 Deadline feasibility with fixed duration.
EV027 Resource lock window conflict in timeline.
EV028 Temporal rule contradiction between policies.
EV029 Temporal query with missing timestamp (clarification expected).
EV030 Temporal what-if comparison in two snapshots.

### T4: Graph and Reachability Reasoning

EV031 Direct reachability in directed graph.
EV032 Reachability through intermediate nodes.
EV033 Unreachable target due to missing edge.
EV034 Blocked edge policy preventing path.
EV035 Cycle detection consistency case.
EV036 Bipartite check on small graph instance.
EV037 Triangle 2-coloring unsat case.
EV038 Short witness path extraction request.
EV039 Alternative route under forbidden node constraint.
EV040 Incremental graph expansion from unknown to sat.

### T5: Planning and Resource Feasibility

EV041 Single resource overload detection.
EV042 Multi-resource feasible assignment.
EV043 Dependency plan with impossible ordering.
EV044 Plan validity with optional task branch.
EV045 Crew capacity plus skill constraint.
EV046 Warehouse pick-pack-ship timing feasibility.
EV047 Energy budget feasibility for production batch.
EV048 Robot safety invariant violation in step plan.
EV049 Plan repair request after one rule change.
EV050 Compare two feasible plans by constraint slack.

### T6: Policy, Authorization, and Compliance

EV051 Role-based permission entitlement.
EV052 Permission denied due to missing role.
EV053 Group inheritance grants access.
EV054 Explicit deny overrides inherited allow.
EV055 Segregation-of-duty conflict on same user.
EV056 Data residency policy check by region.
EV057 Contract clause incompatibility detection.
EV058 Eligibility rule with two numeric thresholds.
EV059 Audit query asking for minimal violating facts.
EV060 Policy update re-evaluation of previous query.

### T7: Knowledge Ingestion and Provenance

EV061 Ingest one statement and verify entailment link.
EV062 Ingest two statements from same source with offsets.
EV063 Ingest contradictory statement and mark contested.
EV064 Source trace query for one derived claim.
EV065 Merge fragments from two documents with tags.
EV066 Reject malformed SMT payload at validation gate.
EV067 Signature mismatch detection in proposal.
EV068 Layer promotion from proposed to accepted.
EV069 Layer rollback after failed consistency check.
EV070 Ask response decoder to cite exact fragment IDs.

### T8: Ambiguity and Clarification Loops

EV071 Ambiguous quantifier interpretation (all vs some).
EV072 Polysemous term requiring user disambiguation.
EV073 Missing domain scope for a policy question.
EV074 Conflicting user statements requiring confirmation.
EV075 Numeric unit ambiguity (days vs hours).
EV076 Entity identity ambiguity (same name, two entities).
EV077 Implicit negation ambiguity in natural language.
EV078 Query objective ambiguity (prove vs find example).
EV079 Clarification loop resolved then successful entailment.
EV080 Clarification refused leading to safe unknown response.

### T9: Worlds, Snapshots, and Fork Comparison

EV081 Create world and baseline snapshot.
EV082 Fork world with alternative axiom.
EV083 Run same query in parent and child worlds.
EV084 Compare verdict difference across branches.
EV085 Compare active axiom sets across snapshots.
EV086 Rollback to prior snapshot and re-query.
EV087 Two-level fork tree with independent updates.
EV088 Cross-world explanation with provenance references.
EV089 Branch contamination prevention check.
EV090 Merge-intent simulation reported as unsupported for MVP.

### T10: Unknown Handling and Robustness

EV091 Timeout budget reached returns unknown safely.
EV092 Atom budget reached triggers controlled expansion.
EV093 Solver backend fails over from Z3 to CVC5 strategy.
EV094 Large candidate set reduced by intuition ranking.
EV095 Response decoder refuses unsupported claim.
EV096 Missing model artifact handled without crash.
EV097 Unsat core unavailable fallback explanation path.
EV098 Deterministic replay of same query and snapshot.
EV099 Stress run with 50 incremental queries in one world.
EV100 End-to-end regression pack combining ingestion, fork, query, and comparison.

## Case Data Contract

Each evaluation case should be stored as a structured object with at least:

`id`, `track`, `title`, `input`, `worldSetup`, `expectedVerdict`, `expectedEvidenceType`, `allowedAmbiguities`, `budgets`, `notes`.

## WorldSetup Action DSL

`worldSetup` is a declarative list of `WorldAction` objects so the runner can replay setup deterministically before each case query.

Minimal `WorldAction` shape:

`action`, `params`, optional `captureAs`.

Required MVP actions:

- `createWorld` (`worldId`, optional `fromSnapshotId`),
- `setStrategy` (`smtStrategy`, `intuitionStrategy`, `vsaRepresentation`, `llmProfile`),
- `setWorldPolicy` (`sensitivity`, redaction and retention policy flags),
- `ingestProposal` (`formalProposal` object compliant with DS004),
- `promoteProposal` (`proposalId`, optional `expectedRegistryVersion` compare-and-swap guard),
- `snapshot` (`worldId`, optional `label`, optional `captureAs`),
- `forkWorld` (`fromWorldId`, `fromSnapshotId`, `newWorldId`),
- `switchWorld` (`worldId`).

Example:

```json
{
  "id": "EV081",
  "track": "T9",
  "worldSetup": [
    { "action": "createWorld", "params": { "worldId": "w_main" } },
    {
      "action": "ingestProposal",
      "params": { "formalProposalRef": "fixtures/proposals/ev081_base.json" },
      "captureAs": "p1"
    },
    { "action": "promoteProposal", "params": { "proposalId": "$p1", "targetState": "accepted" } },
    { "action": "snapshot", "params": { "worldId": "w_main", "label": "baseline" }, "captureAs": "s1" },
    { "action": "forkWorld", "params": { "fromWorldId": "w_main", "fromSnapshotId": "$s1", "newWorldId": "w_alt" } },
    { "action": "switchWorld", "params": { "worldId": "w_alt" } }
  ]
}
```

The runner must fail fast on unknown `action` values or unresolved references (`$name`) to keep suite behavior deterministic.

Each execution result should include:

`caseId`, `combinationId`, `status`, `elapsedMs`, `verdict`, and optional `error`.

Run-level metadata should include `llmInvocationMode` and cache-path identifiers used for SMT artifacts.

Replay-focused cases (for example EV098) must execute in IR replay mode (`FormalProposal` + solver only), without live LLM regeneration.

## Execution and Scoring

Primary scoring dimensions:

- verdict correctness,
- evidence fidelity (model/core/provenance mapping),
- clarification quality for ambiguous inputs,
- stability across repeated runs,
- budget-respecting behavior (`unknown` when required),
- comparative speed per strategy combination.

Comparative speed should be reported as both absolute average time per case and relative speed ratio against the fastest combination in the same run.

## Runner Script Contract

The orchestration entry point is `eval/runEval.mjs`.

Required behavior:

- run `smoke` profile with default combinations,
- run `all` profile for full combination sweep,
- include both Intuition strategies (`NoIntuition`, `VSAIntuition`),
- include both baseline VSA/HDC representations (HRR and Binary HDC) for `VSAIntuition`,
- default to `cached-smt` mode with no live LLM calls,
- support opt-in `--llm` mode for live generation tests,
- when `--llm` is enabled, include both Achilles `fast-default` and `deep-default` LLM profiles,
- emit machine-readable result artifacts under `eval/results/`.

## Delivery Stages

Stage 1 delivers `EV001-EV040` for core logical and constraint confidence.

Stage 2 delivers `EV041-EV080` for operational workflows and ambiguity.

Stage 3 delivers `EV081-EV100` for world management and robustness stress.
