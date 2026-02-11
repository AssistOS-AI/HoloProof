# DS003 - Worlds, Knowledge Base, and Forking

## World Model

A world is an isolated reasoning session. It contains a layered knowledge base, reasoning configuration, intuition index, symbol registry, and conversation history. All ingestion and querying operations run against one active world at a time.

![World snapshot and fork diagram](../assets/svgs/world-forking.svg)

Diagram summary: a base world evolves through snapshots, then branches into independent worlds for alternative hypotheses. Each branch can diverge safely without contaminating the original state.

## Knowledge Base Layers

Knowledge is stored as versioned fragments with stable identifiers and provenance. Each fragment keeps source metadata (document ID, offsets, timestamp), formal payload, semantic tags, and one lifecycle state: `proposed`, `accepted`, or `contested`.

The system never auto-promotes LLM-generated formalizations directly into stable truth. Formal payloads begin as `proposed`, pass structural and solver checks, and become `accepted` only after validation succeeds.

## Formal Proposal Lifecycle

Every ingestion/query formalization enters the world as a `FormalProposal` object and receives a stable `proposalId`.

Lifecycle transitions are strict:

- `proposed -> accepted` only after schema validation, symbol-registry merge validation, and isolated solver sanity check.
- `proposed -> contested` when validation fails or conflicts cannot be resolved safely.
- `contested -> proposed` only through explicit user or orchestrator revision; there is no automatic recovery.

Each accepted fragment stores `proposalId` and `registrySnapshotId` so downstream reasoning and explanations remain reproducible.

Accepted fragments are immutable in MVP. Corrections are done through new proposals and forked worlds, not by mutating accepted history in place.

## Symbol Registry Contract

Each world owns a versioned symbol registry used by validators and LLM encoders. The registry tracks declared sorts, constants, functions, and predicates with canonical signatures and lightweight semantic metadata.

Minimal entry shape:

```json
{
  "symbol": "eligible",
  "kind": "predicate",
  "arity": 1,
  "argSorts": ["Person"],
  "resultSort": "Bool",
  "semanticHint": "person qualifies for program benefits",
  "usageCount": 12,
  "declaredIn": "proposal:fp_0021",
  "status": "active"
}
```

Conflict rules are deterministic:

- exact same declaration is idempotent and accepted,
- same symbol name with different `kind` or incompatible arity/signature is a hard conflict,
- unresolved conflicts block promotion to `accepted`.

Sort aliasing is supported as explicit metadata (`Human -> Person`, `Individual -> Person`) and is used for compatibility checks and warning generation.

Registry merge can emit warnings (without hard rejection) for likely semantic duplicates, such as a new predicate with same kind/arity/sorts as an existing one but different name.

LLM encoding requests must receive a compact registry snapshot including semantic hints, alias metadata, and explicit symbol-reuse rules so new proposals stay signature-consistent by design.

## Acceptance and Conflict Discipline

Validation applies three gates before acceptance: safe SMT-LIB2 syntax, symbol-signature consistency through the world registry, and a solver sanity check in an isolated layer. If a proposal introduces inconsistency, the fragment set is marked `contested` and kept outside the stable layer.

Within one world, proposal promotion is serialized. Optional compare-and-swap checks may require an expected registry version; if the version advanced, promotion is rejected and must be retried against fresh state.

When conflict appears, the orchestrator asks targeted clarification questions instead of forcing hidden assumptions. This behavior is required for preserving logical integrity and user trust.

## Snapshot and Fork Semantics

A snapshot captures a world state at a specific point in time, including KB layers and symbol-registry version. A fork creates a new world from an existing snapshot and writes future changes into new layers. This enables controlled experimentation with alternative interpretations, domain restrictions, or temporary assumptions.

Comparing worlds is a first-class operation. Comparison reports should focus on changed active axioms, symbol-registry deltas, query verdict differences, and supporting solver artifacts.

Default comparison visibility is fragment IDs only. Restricted-provenance fragments should remain redacted unless explicit policy allows detailed disclosure.
