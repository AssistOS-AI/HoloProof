# DS006 - Chat and Examples Experience

## Objective

Define a chat interface that demonstrates HoloProof as a formal-reasoning assistant, not a generic text chatbot. The interface must support both normal chat flow and guided example playback.

## Two-Tab Interaction Model

The chat UI has two top-level tabs: `Chat` and `Examples`.

`Chat` is the primary conversation space where user prompts, formalization traces, solver-backed reasoning outcomes, and final responses are shown in chronological order.

`Examples` is a curated catalog of ready-to-run prompts. It helps users understand ideal prompt patterns and expected reasoning structure.

## Chat Tab Requirements

The Chat tab must show three information layers for each meaningful assistant turn: formalization intent, formal reasoning trace, and final solver-aligned answer.

The user should be able to run examples directly into chat without losing context. Example playback should appear as real turns, not as hidden metadata.

When interactive runtime is implemented, Chat tab logic should call SDK interfaces from `src/sdk/` (world management, proposal lifecycle, reasoning traces) instead of embedding domain rules in UI code.

Controls required for MVP demonstration mode:

- `Load Next Example`
- `Load All Remaining`
- `Reset Demo Chat`

## Examples Tab Requirements

The Examples tab must expose at least 30 diverse examples covering logic, arithmetic, scheduling, policy checks, consistency checks, reachability, temporal constraints, and world comparison.

Each example card includes:

- problem label,
- ideal prompt formulation,
- formalization intent,
- expected reasoning shape,
- expected answer style.

Each card must offer a direct action to inject that example into the Chat tab.

## Prompt Quality Guidance

The Examples tab is not only a dataset browser; it is a prompt-writing guide. Every example should reinforce good formalization habits: explicit facts, explicit objective, explicit scope, and explicit expected output type.

## Demonstration-Only Constraint

Example playback in documentation mode can be deterministic and scripted, but its transcript format must mirror production style so users understand how formal reasoning will be presented in real runs.

## Reference Implementation

The documentation-level implementation is provided in `docs/usage-guide.html` with the same two-tab model and example playback controls.
