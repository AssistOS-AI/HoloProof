/*
 * Orchestrator — thin bridge between the chat UI and the SDK.
 * Manages WorldManager, proposal lifecycle, and demo-mode reasoning.
 */
import { DEMO_SCENARIOS } from './demo-scenarios.mjs';

/* ── SDK imports (rewritten paths for browser ES modules) ── */
import { validateFormalProposal, collectReferencedSymbols } from '../src/sdk/formalProposal.mjs';
import { SymbolRegistry } from '../src/sdk/symbolRegistry.mjs';
import { WorldManager } from '../src/sdk/worldManager.mjs';
import { validateAnchoredExplanation, buildEvidenceAnchorSet, buildVerdictNarrationPrefix } from '../src/sdk/response/evidenceAnchoring.mjs';
import { decideExpansion } from '../src/sdk/reasoning/expansionPolicy.mjs';
import { applyTracePolicy } from '../src/sdk/observability/tracePolicy.mjs';

/* ── Strategy constants ── */
export const STRATEGY_OPTIONS = {
    smtStrategy: [
        { id: 'smt-z3-incremental-refutation', label: 'Z3 — Incremental Refutation' },
        { id: 'smt-z3-incremental-model', label: 'Z3 — Model Finding' },
        { id: 'smt-cvc5-incremental-refutation', label: 'CVC5 — Incremental Refutation' },
        { id: 'smt-cvc5-incremental-model', label: 'CVC5 — Model Finding' },
    ],
    intuitionStrategy: [
        { id: 'no-intuition', label: 'No Intuition (full scan)' },
        { id: 'vsa-intuition', label: 'VSA Intuition (candidate pre-selection)' },
    ],
    vsaRepresentation: [
        { id: 'vsa-disabled', label: 'Disabled' },
        { id: 'vsa-hrr-cosine-topk', label: 'HRR Cosine Top-K' },
        { id: 'vsa-hdc-binary-hamming-topk', label: 'HDC Binary Hamming Top-K' },
    ],
    llmProfile: [
        { id: 'llm-cached', label: 'Cached SMT (no LLM)' },
        { id: 'llm-fast-default', label: 'LLM Fast' },
        { id: 'llm-deep-default', label: 'LLM Deep' },
    ],
};

/* ── Orchestrator class ── */
export class ChatOrchestrator {
    constructor() {
        this.manager = new WorldManager();
        this.worldId = 'world_chat';
        this.manager.createWorld(this.worldId);
        this._proposalCounter = 0;
        this._loadedScenarioId = null;
        this._strategy = {
            smtStrategy: STRATEGY_OPTIONS.smtStrategy[0].id,
            intuitionStrategy: STRATEGY_OPTIONS.intuitionStrategy[0].id,
            vsaRepresentation: STRATEGY_OPTIONS.vsaRepresentation[0].id,
            llmProfile: STRATEGY_OPTIONS.llmProfile[0].id,
        };
        this.manager.setStrategy(this.worldId, this._strategy);
    }

    /* ── Public API ── */

    getScenarios() {
        return DEMO_SCENARIOS.map(s => ({
            id: s.id,
            title: s.title,
            category: s.category,
            description: s.description,
            problemCount: s.problems.length,
        }));
    }

    getScenarioDetail(scenarioId) {
        return DEMO_SCENARIOS.find(s => s.id === scenarioId) || null;
    }

    setStrategy(key, value) {
        this._strategy[key] = value;
        try {
            this.manager.setStrategy(this.worldId, this._strategy);
        } catch { /* world may not exist during reset */ }
        return { ...this._strategy };
    }

    getStrategy() {
        return { ...this._strategy };
    }

    getWorldInfo() {
        try {
            return this.manager.getWorld(this.worldId);
        } catch {
            return null;
        }
    }

    resetWorld() {
        if (this.manager.hasWorld(this.worldId)) {
            /* Recreate since WorldManager lacks deleteWorld */
            this.manager = new WorldManager();
        }
        this.worldId = 'world_chat';
        this.manager.createWorld(this.worldId);
        this._proposalCounter = 0;
        this._loadedScenarioId = null;
        this.manager.setStrategy(this.worldId, this._strategy);
        return { status: 'reset', worldId: this.worldId };
    }

    /**
     * Load knowledge from a demo scenario into the world.
     * Returns { loaded, fragments, warnings, registryVersion }
     */
    loadScenarioKnowledge(scenarioId) {
        const scenario = DEMO_SCENARIOS.find(s => s.id === scenarioId);
        if (!scenario) return { error: `Unknown scenario: ${scenarioId}` };

        const results = [];
        for (const proposal of scenario.knowledge) {
            const pid = this._nextProposalId();
            const p = { ...proposal, proposalId: pid, worldId: this.worldId };

            /* Validate */
            const validation = validateFormalProposal(p);
            if (!validation.valid) {
                results.push({ proposalId: pid, state: 'invalid', errors: validation.errors });
                continue;
            }

            /* Ingest + promote */
            this.manager.ingestProposal(this.worldId, p);
            const promoted = this.manager.promoteProposal(this.worldId, pid);
            results.push({
                proposalId: pid,
                state: promoted.state,
                registryVersion: promoted.registryVersion,
                conflicts: promoted.conflicts,
                warnings: promoted.warnings,
                declarationCount: proposal.declarations.length,
                assertionCount: proposal.assertions.length,
            });
        }

        this._loadedScenarioId = scenarioId;

        const worldInfo = this.manager.getWorld(this.worldId);
        return {
            scenarioId,
            title: scenario.title,
            loaded: results,
            fragmentCount: worldInfo.fragmentCount,
            registryVersion: worldInfo.registryVersion,
        };
    }

    /**
     * Process a user query (in demo mode, matches against loaded scenario problems).
     * Returns the full reasoning response object.
     */
    processQuery(userText) {
        const scenario = this._loadedScenarioId
            ? DEMO_SCENARIOS.find(s => s.id === this._loadedScenarioId)
            : null;

        /* Try to match against a scenario problem */
        let matched = null;
        if (scenario) {
            matched = this._findBestMatch(userText, scenario.problems);
        }

        /* If no scenario loaded or no match, try all scenarios */
        if (!matched) {
            for (const s of DEMO_SCENARIOS) {
                matched = this._findBestMatch(userText, s.problems);
                if (matched) {
                    /* Auto-load scenario knowledge if not already loaded */
                    if (this._loadedScenarioId !== s.id) {
                        this.loadScenarioKnowledge(s.id);
                    }
                    break;
                }
            }
        }

        if (!matched) {
            return this._buildUnknownResponse(userText);
        }

        return this._buildDemoResponse(userText, matched);
    }

    /* ── Private helpers ── */

    _nextProposalId() {
        this._proposalCounter += 1;
        return `fp_chat_${String(this._proposalCounter).padStart(4, '0')}`;
    }

    _findBestMatch(userText, problems) {
        const normalizedInput = userText.toLowerCase().replace(/[^a-z0-9\s]/g, '');
        const inputTokens = new Set(normalizedInput.split(/\s+/).filter(Boolean));

        let bestMatch = null;
        let bestScore = 0;

        for (const problem of problems) {
            const promptTokens = problem.prompt.toLowerCase().replace(/[^a-z0-9\s]/g, '').split(/\s+/).filter(Boolean);
            let score = 0;
            for (const token of promptTokens) {
                if (inputTokens.has(token)) score += 1;
            }
            /* Normalize */
            const normalized = promptTokens.length > 0 ? score / promptTokens.length : 0;
            if (normalized > bestScore && normalized > 0.3) {
                bestScore = normalized;
                bestMatch = problem;
            }
        }

        return bestMatch;
    }

    _buildDemoResponse(userText, problem) {
        const result = problem.simulatedResult;
        const strategy = this.getStrategy();
        const worldInfo = this.getWorldInfo();

        /* Build evidence anchoring */
        const anchorSet = buildEvidenceAnchorSet(result.evidence || {});
        const prefix = buildVerdictNarrationPrefix(result.verdict);

        /* Build trace */
        const trace = applyTracePolicy({
            createdAt: new Date().toISOString(),
            query: userText,
            formalTarget: problem.formalTarget,
            verdict: result.verdict,
            interpretation: result.interpretation,
            solverArtifacts: {
                model: result.evidence?.modelKeys ? Object.fromEntries(result.evidence.modelKeys.map(k => [k, '…'])) : null,
                unsatCore: result.evidence?.unsatCoreIds || null,
            },
        }, this.manager.getWorldPolicy(this.worldId));

        return {
            type: 'reasoning-response',
            userQuery: userText,
            strategy,
            worldInfo: worldInfo ? {
                worldId: worldInfo.worldId,
                registryVersion: worldInfo.registryVersion,
                fragmentCount: worldInfo.fragmentCount,
                proposalCount: worldInfo.proposalCount,
            } : null,
            formalization: {
                target: problem.formalTarget,
                status: 'simulated',
            },
            reasoning: {
                verdict: result.verdict,
                interpretation: result.interpretation,
                trace: result.reasoning,
                expansionRounds: 0,
            },
            answer: {
                prefix,
                text: result.answer,
            },
            evidence: {
                anchorSet: [...anchorSet],
                trace,
            },
        };
    }

    _buildUnknownResponse(userText) {
        const strategy = this.getStrategy();
        return {
            type: 'unknown-query',
            userQuery: userText,
            strategy,
            formalization: {
                target: 'No matching formalization found in loaded scenarios.',
                status: 'unmatched',
            },
            reasoning: {
                verdict: 'unknown',
                interpretation: 'no-match',
                trace: `The query "${userText}" could not be matched to any known demo scenario.\n\nIn production, this is where the LLMEncoder would:\n1. Receive the symbol registry context\n2. Generate a FormalProposal from your natural language\n3. Validate it through schema + registry gates\n4. Emit SMT-LIB2 and invoke the solver\n\nFor now, try loading a demo scenario from the Knowledge tab and ask one of its problems.`,
                expansionRounds: 0,
            },
            answer: {
                prefix: 'Demo mode limitation:',
                text: 'This query does not match any loaded scenario. Load a demo scenario from the Knowledge tab to see reasoning in action.',
            },
            evidence: { anchorSet: [], trace: null },
        };
    }
}
