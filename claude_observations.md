# Claude Observations: QA, Security, and Edge-Case Risks

Deep analysis of HoloProof specifications for quality assurance gaps, security concerns, race conditions, trust boundary violations, and subtle failure modes that could surface during implementation or production use.

---

## 1. Semantic Symbol Unification Problem

**Severity: HIGH** | **Affects: DS003, DS004** | **Category: Data Integrity**

### The Problem

The Symbol Registry in DS003 prevents **structural conflicts** (same name, incompatible signature) but does not prevent **semantic duplication** (different name, same real-world concept).

**Concrete scenario:**

1. Fragment 1 is ingested, LLM creates `(declare-fun eligible (Person) Bool)` → accepted
2. Fragment 2 is ingested later, LLM invents `(declare-fun qualifies (Person) Bool)` → also accepted (different name, no conflict)
3. Now facts about eligibility are split across two unconnected predicates
4. A query `eligible(Ana)` will find no facts from Fragment 2, even though the user's intent was the same concept

This degrades silently. No error, no conflict, no warning. The knowledge base just becomes **semantically fragmented**.

### Why the Current Spec Doesn't Prevent It

- The registry snapshot given to the LLM contains `name + signature` but no semantic descriptions
- There is no prompt contract requiring the LLM to prefer existing symbols
- The validation gates check structural compatibility, not semantic equivalence
- Sort aliasing is absent (`Person` vs `Human` vs `Individual` are all accepted as distinct sorts)

### Proposed Additions

**DS003 — Registry Semantic Metadata:**

Add a `semanticHint` field to registry entries:
```json
{
  "symbol": "eligible",
  "kind": "predicate",
  "argSorts": ["Person"],
  "resultSort": "Bool",
  "semanticHint": "whether a person qualifies for program benefits",
  "declaredIn": "proposal:fp_0021",
  "usageCount": 3,
  "status": "active"
}
```

**DS003 — Sort Aliasing Declaration:**

Allow explicit equivalence: `{ "aliasOf": "Person", "aliases": ["Human", "Individual"] }`. When the LLM proposes a new sort, the registry gate should check if it's an alias candidate and ask for clarification.

**DS004 — Encoding Prompt Contract:**

The prompt sent to the LLM with registry context must include:
- "REUSE existing symbols when they match the concept you are encoding"
- "Do NOT create synonyms for predicates/functions already in the registry"
- semantic hints, not just structural signatures

**DS003 — Near-Duplicate Detection Gate:**

Add an optional validation gate that flags suspicious new declarations:
- New predicate with same arity and compatible sorts as an existing one → warning
- New sort with a name that is a common synonym of an existing sort → warning

These warnings should trigger clarification, not auto-rejection.

---


## 3. SMT-LIB2 Injection Through Expression IR

**Severity: MEDIUM** | **Affects: DS004** | **Category: Security**

### The Problem

The FormalProposal IR uses string fields for symbol names (`"name": "eligible"`, `"symbol": "student"`). The deterministic emission step converts these to SMT-LIB2 text. If a symbol name contains SMT-LIB2 metacharacters or embedded commands, the emitted output could break the solver or execute unintended commands:

```json
{ "kind": "const", "name": ")(check-sat)(exit)(set-logic" }
```

This would emit something like:
```smt2
(declare-const )(check-sat)(exit)(set-logic Bool)
```

### Why Current Spec Is Insufficient

DS004 mentions "safe-command filtering" in the emission gate and "reserved symbol prefixes blocked", but doesn't define:
- What characters are legal in symbol names
- Whether parentheses, semicolons, pipes, or quotes are allowed
- A positive whitelist for the symbol name grammar

### Proposed Additions

**DS004 — Symbol Name Grammar:**

Define a strict symbol name regex: `^[a-zA-Z_][a-zA-Z0-9_]*$` (or SMT-LIB2's `<simple_symbol>` grammar, which excludes parentheses, pipes, and whitespace). Any name that doesn't match must be rejected at the schema gate.

**DS004 — Emission Sanitization:**

The emission step must:
- Validate every symbol name against the grammar before emitting
- Escape or quote names if using SMT-LIB2 quoted symbols (`|name with spaces|`), with explicit rules for what is permitted
- Block any name containing SMT-LIB2 commands (`check-sat`, `exit`, `set-logic`, `set-option`, etc.)

---

## 4. Solver Resource Exhaustion (Memory DoS)

**Severity: MEDIUM** | **Affects: DS004, DS005** | **Category: Security / Robustness**

### The Problem

DS004 specifies budgets for timeout and active atom count, but not for **memory**. A pathological SMT problem can consume gigabytes of RAM before timing out, especially with:
- Large quantifier instantiation chains
- Unbounded model generation
- Complex arithmetic with bitvectors

A single malicious or accidentally expensive query could crash the solver subprocess and potentially the host system.

### Why Current Spec Is Insufficient

DS005's session lifecycle handles process crashes (restart + replay), but doesn't address prevention. The "expansion loop" from DS004 (unknown → expand candidates → retry) makes this worse: each retry adds more assertions, increasing memory pressure.

### Proposed Additions

- **Memory budget**: add a `maxMemoryMB` parameter to `openSession` config, enforced via solver options (`(set-option :memory-limit ...)` where supported) or OS-level `ulimit`
- **Expansion loop cap**: specify a maximum number of expansion rounds (not just atom count) to prevent runaway retries
- **Process isolation**: consider spawning solver subprocesses in cgroups or containers with hard memory limits
- **Pre-flight complexity check**: before sending to solver, estimate assertion complexity (quantifier depth, term count) and reject or warn on obviously expensive problems

---

## 5. Race Conditions in Concurrent Proposal Submission

**Severity: MEDIUM** | **Affects: DS003, DS005** | **Category: Data Integrity**

### The Problem

The spec says "all ingestion and querying operations run against one active world at a time" (DS003), but doesn't address **concurrency within a world**. If two proposals are submitted simultaneously:

1. Both read the registry snapshot at time T
2. Both pass registry validation against the T-state
3. Proposal A adds symbol `eligible(Person)`
4. Proposal B also adds symbol `eligible(Person)` — idempotent, fine.
5. But: Proposal A adds `income(Person) → Int` and Proposal B adds `income(Person) → Real` — both pass against T-state, but conflict with each other

### Why Current Spec Is Insufficient

The registry conflict rules are defined for sequential insertion. There is no mention of:
- Optimistic locking or compare-and-swap on the registry version
- Serialization of proposal validation within a world
- What happens when two proposals are valid independently but conflict with each other

### Proposed Additions

- **Serialized validation**: proposals must be validated and committed in strict sequence within a world (easiest MVP solution)
- **Registry version stamp**: each proposal records the `registryVersion` it was validated against; commit rejects if version has advanced since validation
- If parallelism is desired later: define an optimistic-lock retry protocol

---

## 6. Session Replay After Crash Can Introduce Inconsistency

**Severity: MEDIUM** | **Affects: DS005** | **Category: Robustness**

### The Problem

DS005 says that after a solver process crash, the adapter should "restart process and replay stable accepted assertions from journaled state." But:

1. The pre-crash session may have had `push/pop` scopes with temporary assumptions
2. If the crash happened mid-check-sat, the `push` stack is lost
3. Replaying only "stable accepted assertions" drops the reasoning context that was active at crash time
4. The query that was running will silently get a **different** result after replay (because the context is different)

### Why This Matters

The spec correctly says "recovery never replays transient branch assumptions blindly." But this means any query that was using temporary assumptions at crash time will **fail silently** — the replayed session has a different state, and the next `check-sat` might return a different verdict without any indication that context was lost.

### Proposed Additions

- **Session health flag**: after replay, the session must be marked as "recovered" and any pending check-sat must be re-dispatched from the orchestrator level, not silently retried
- **Crash notification**: the adapter must emit a structured event (`session-recovered`) that the orchestrator can react to (e.g., re-run the query from scratch)
- **Query idempotency contract**: specify that queries must be safe to re-run from the top after a crash, meaning the orchestrator must store enough state to reconstruct the full push/pop/assert sequence

---

## 7. Observability Data Contains Sensitive Information

**Severity: MEDIUM** | **Affects: DS005** | **Category: Security / Privacy**

### The Problem

DS005 mandates that every query persists a trace containing: "world ID, snapshot ID, formal query, active fragment IDs, chosen strategy, budget values, elapsed timing, and solver artifacts."

If HoloProof is used for sensitive domains (contracts, HR policies, medical eligibility, financial compliance), these traces contain:
- The full text of user queries
- The formalized rules (which may contain proprietary logic)
- Solver models (which may contain satisfying assignments revealing private data)
- Unsat cores (which reveal which specific rules caused a conflict)

### Why Current Spec Is Insufficient

There is no mention of:
- Trace retention policies
- Access control on audit data
- Data classification for traces
- Redaction rules for sensitive fields

### Proposed Additions

- **Trace classification**: mark traces with the sensitivity level of the originating world
- **Retention policy**: define default TTL for traces (e.g., 30 days for debug traces, indefinite for compliance audit)
- **Access control**: traces should inherit the access rights of the world they belong to
- **Redaction support**: allow worlds to be configured with redaction rules that strip specific fields from traces before persistence (e.g., strip model values for privacy-sensitive domains)

---

## 8. Unsat Core Information Disclosure

**Severity: LOW-MEDIUM** | **Affects: DS004, DS005** | **Category: Security**

### The Problem

When a query returns `unsat`, the system may extract and display unsat cores — the minimal set of axioms that cause the contradiction. In a multi-user or multi-tenant scenario, these cores **reveal** which specific rules or facts are active in the knowledge base.

Example: User A asks "Can contractor X access the finance system?" → `unsat`. The unsat core reveals the rule `contractors cannot access finance systems if hired through agency Y` — information that User A might not be authorized to see.

### Proposed Mitigations

- **Core visibility policy**: define whether unsat cores are shown verbatim, summarized, or filtered by the ResponseDecoder based on user access level
- **Fragment-level access control**: a fragment can be marked as "restricted provenance" — its ID can appear in diagnostics but its content should be redacted
- In MVP, this may be deferred, but the spec should acknowledge it as a future concern

---

## 9. LLM Context Window Overflow for Large Registry

**Severity: MEDIUM** | **Affects: DS003, DS004** | **Category: Scalability**

### The Problem

DS003 says the LLM receives a "compact registry snapshot" for symbol reuse. But as the knowledge base grows, the registry could become very large. A world with 500+ symbols, each with sort/arity/semantic hints, could easily exceed the effective context window budget for the encoding prompt.

If the registry is truncated to fit, the LLM loses visibility of existing symbols and will create duplicates (see Observation #1).

### Proposed Additions

- **Registry summarization strategy**: define how to select the most relevant registry subset for a given encoding request (e.g., symbols from same source document, same semantic tags, or via VSA similarity ranking)
- **Maximum registry context budget**: specify a target size (e.g., "top 100 most relevant symbols" or "symbols used in the last N proposals")
- The Intuition module could potentially help here: use VSA similarity to select relevant registry entries for the encoding context

---

## 10. Deterministic Replay Is Not Truly Deterministic With LLM

**Severity: LOW** | **Affects: DS005, DS010** | **Category: QA / Reproducibility**

### The Problem

DS005's observability model and DS010's eval suite assume deterministic replay ("EV098: Deterministic replay of same query and snapshot"). But the pipeline includes LLM calls, which are **inherently non-deterministic** (even with temperature=0, model versions change, and API responses vary).

### Why This Matters

- Test reproducibility breaks across model updates
- Audit trail replay may not produce the same FormalProposal
- "Stability across repeated runs" (DS010 scoring) becomes hard to measure

### Current Mitigation

DS010 already adds `cached-smt` mode (no live LLM calls), which solves this for evaluation. But for **production** replay and audit, the spec doesn't address it.

### Proposed Additions

- **FormalProposal caching**: every accepted FormalProposal is stored as part of the fragment (this is already implied). Replay should use the stored proposal, not re-generate via LLM.
- **Replay contract**: explicitly state that deterministic replay operates on stored IR + solver, never on re-invoked LLM. The LLM is only invoked for new queries, not for replay.
- This is probably already the intent, but making it explicit avoids confusion.

---

## 11. Fragment Rollback Cascading Effects

**Severity: MEDIUM** | **Affects: DS003** | **Category: Data Integrity**

### The Problem

DS003 mentions that a snapshot can be rolled back to and that contested fragments are kept outside the stable layer. But what happens when an **accepted** fragment is later found to be problematic?

Scenario:
1. Fragment A (`eligible(Person) → Bool`) accepted
2. Fragment B (`student(Ana)`, `eligible(Ana)`) accepted — uses symbols from A
3. Fragment A is discovered to be wrong and needs to be removed
4. Fragment B is now semantically orphaned — it references symbols from A, but A is gone

### Why Current Spec Is Insufficient

The spec covers `proposed → contested` and `proposed → accepted`, but not:
- `accepted → withdrawn` (what triggers this?)
- Dependency tracking between fragments
- Cascading invalidation when a foundational fragment is removed
- Whether withdrawal is even allowed, or if the only option is forking a corrected world

### Proposed Additions

- **Dependency graph**: track which fragments depend on which symbol declarations
- **Withdrawal policy**: either (a) fragments are immutable once accepted (corrections go through new world/fork), or (b) define a cascading withdrawal protocol that marks dependents as `contested`
- For MVP, option (a) is simpler and aligns with the "fork for alternatives" philosophy

---

## 12. ResponseDecoder Hallucination Risk

**Severity: MEDIUM** | **Affects: DS004** | **Category: QA / Trust**

### The Problem

DS004 says `ResponseDecoder` receives "only approved evidence" and "every explanatory claim must map back to that evidence." But the ResponseDecoder **uses an LLM** to generate natural-language explanations. The LLM might:

- Add plausible-sounding reasoning steps that aren't in the solver artifacts
- Misinterpret the solver model and produce an incorrect explanation
- Generate confident language about uncertain results

### Why This Matters

The entire trust model depends on the ResponseDecoder faithfully translating solver output. If it hallucinates, the user receives a formally-backed verdict with a **misleading explanation** — arguably worse than no explanation at all, because the verdict creates false confidence.

### Proposed Additions

- **Evidence anchoring contract**: the ResponseDecoder prompt must use a structured template where each claim is explicitly linked to a specific artifact (fragment ID, axiom from model, core element)
- **Explanation validation gate**: a lightweight post-processing step that verifies every claim in the response can be traced to a concrete artifact. Claims without anchors are either stripped or flagged.
- **Uncertainty language rules**: define how the decoder should phrase explanations for `unknown` verdicts or partial evidence (e.g., "Based on available formalization..." rather than definitive statements)

---


## 14. Subprocess Stdin/Stdout Desynchronization

**Severity: MEDIUM** | **Affects: DS005** | **Category: Robustness**

### The Problem

DS005 specifies that solver communication happens through stdin/stdout pipes. In incremental mode, the adapter sends commands and reads responses. But:

- SMT solvers don't always produce exactly one response per command
- Some commands (like `(get-model)`) produce multi-line responses
- Error messages may appear on stderr or interleaved with stdout
- If a command produces unexpected output, the read/write streams desynchronize and all subsequent commands get wrong responses

DS005 mentions "command sequence ID" for correlation, but SMT-LIB2 has **no built-in correlation mechanism** — commands don't have IDs, and responses don't echo which command they answer.

### Proposed Additions

- **Sentinel-based synchronization**: after each command, send a known-output command (like `(echo "HP_SYNC_<seqId>")`) and read until the sentinel appears. This guarantees stream alignment.
- **Stderr handling**: define whether stderr is logged, triggers session unhealthy state, or is ignored
- **Response parser contract**: define the expected output format for each command type (`check-sat` → one line, `get-model` → s-expression block, `get-unsat-core` → s-expression block) and how the parser detects response boundaries

---

## 15. Expansion Loop Termination Guarantee

**Severity: LOW-MEDIUM** | **Affects: DS004** | **Category: Robustness**

### The Problem

DS004 describes an expansion loop: if solver returns `unknown`, the orchestrator expands the active set and retries. But:
- There is no specified **termination condition** beyond budget exhaustion
- If the intuition module keeps proposing new candidates, the loop can run for a very long time
- Each expansion increases the solver load, making subsequent `unknown` results more likely (not less)

### Proposed Additions

- **Maximum expansion rounds**: specify a hard cap (e.g., 3 rounds)
- **Stagnation detection**: if two consecutive expansions don't change the verdict, stop
- **Expansion step size**: define how many new candidates are added per round (fixed count or percentage)
- **Escalation policy**: after max expansions with `unknown`, either return `unknown` to user or escalate to a "deep" solver strategy before giving up

---

## Summary Table

| # | Observation | Severity | Category | Spec Gap |
|---|---|---|---|---|
| 1 | Semantic symbol unification | HIGH | Data Integrity | DS003, DS004 |
| 3 | SMT-LIB2 injection via symbol names | MEDIUM | Security | DS004 |
| 4 | Solver memory exhaustion | MEDIUM | Security | DS004, DS005 |
| 5 | Concurrent proposal race conditions | MEDIUM | Data Integrity | DS003, DS005 |
| 6 | Session replay inconsistency | MEDIUM | Robustness | DS005 |
| 7 | Sensitive data in traces | MEDIUM | Privacy | DS005 |
| 8 | Unsat core information disclosure | LOW-MEDIUM | Security | DS004 |
| 9 | Registry context overflow for LLM | MEDIUM | Scalability | DS003, DS004 |
| 10 | LLM non-determinism vs replay | LOW | Reproducibility | DS005 |
| 11 | Fragment rollback cascading | MEDIUM | Data Integrity | DS003 |
| 12 | ResponseDecoder hallucination | MEDIUM | Trust | DS004 |
| 13 | World comparison access leakage | LOW | Security | DS003 |
| 14 | Solver stdin/stdout desync | MEDIUM | Robustness | DS005 |
| 15 | Expansion loop termination | LOW-MEDIUM | Robustness | DS004 |

---

