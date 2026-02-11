# Codex Rejects (Claude Observations)

This file lists proposals from `claude_observations.md` that are not adopted in MVP as-is.

## Rejected or Deferred Items

- Missing-detail observations from summary table (#2 and #13):
  They are acknowledged as concerns, but the source document has no full section content for these two items, so no concrete acceptance criteria could be implemented directly.

- Full automatic synonym unification for symbols/sorts:
  We keep warning-based detection (`possible-semantic-duplicate`, sort alias warnings) instead of automatic semantic merging.
- Automatic merging is high-risk for false positives and can silently corrupt formal meaning.

- SMT quoted-symbol support with escaping (`|name with spaces|`):
  MVP keeps strict identifier grammar only (`^[A-Za-z_][A-Za-z0-9_]*$`) and rejects non-compliant names. This is simpler and safer than introducing escaping logic now.

- Mandatory cgroup/container isolation for solver processes:
  This is deferred to deployment/runtime infrastructure. The SDK/spec includes `maxMemoryMB` budgeting and recovery contracts, but hard OS/container isolation is environment-specific.

- Cascading withdrawal of already accepted fragments:
  MVP keeps accepted fragments immutable. Corrections are handled via new proposals and world forking, avoiding complex dependency invalidation semantics.

- Verbose unsat-core disclosure by default:
  MVP defaults to policy-controlled or redacted unsat-core exposure. Full unrestricted core disclosure is rejected for security/privacy reasons.

## Partially Accepted (Narrowed)

- Concurrency handling:
  Adopted as serialized promotion in world scope with optional compare-and-swap (`expectedRegistryVersion`) checks, not full optimistic-lock retry workflows.

- Response explanation hardening:
  Adopted as evidence-anchor validation utilities and uncertainty phrasing rules; not a full natural-language theorem prover in the decoder.

- Large registry handling:
  Adopted as two deterministic strategies (`usage-topk` and `vsa-similarity-topk`) plus alias metadata; full ontology-level semantic search remains out of MVP scope.
