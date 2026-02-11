import { createIntuitionStrategy } from '../intuition/strategies.mjs';
import { executeFormalQueryPipeline } from '../pipeline/queryPipeline.mjs';
import { encodeFormalProposal } from '../encoding/llmEncoder.mjs';
import { encodeQueryProposal } from '../encoding/queryEncoder.mjs';
import { decodeResponse } from '../response/decoder.mjs';

function createId(prefix = 'id') {
  const random = Math.floor(Math.random() * 1e9);
  return `${prefix}_${String(Date.now())}_${String(random)}`;
}

function solverFromStrategy(strategy = {}) {
  const smtStrategy = String(strategy.smtStrategy || '').toLowerCase();
  if (smtStrategy.includes('cvc5')) {
    return 'cvc5';
  }
  return 'z3';
}

function llmModeFromStrategy(strategy = {}) {
  const profile = String(strategy.llmProfile || '').toLowerCase();
  if (profile.includes('deep')) {
    return 'deep';
  }
  return 'fast';
}

function abortError(message = 'Query execution was cancelled.') {
  const error = new Error(message);
  error.name = 'AbortError';
  return error;
}

function throwIfAborted(signal) {
  if (signal?.aborted) {
    throw abortError();
  }
}

export class ChatOrchestrator {
  constructor(options = {}) {
    if (!options.worldManager) {
      throw new Error('ChatOrchestrator requires worldManager.');
    }
    if (!options.solverAdapter) {
      throw new Error('ChatOrchestrator requires solverAdapter instance.');
    }

    this.worldManager = options.worldManager;
    this.solverAdapter = options.solverAdapter;
    this.llmClient = options.llmClient || null;
    this.currentWorldId = options.defaultWorldId || null;
    this.onEvent = typeof options.onEvent === 'function' ? options.onEvent : null;
  }

  ensureWorld(worldId = null) {
    const target = worldId || this.currentWorldId || 'world_main';
    if (!this.worldManager.hasWorld(target)) {
      this.worldManager.createWorld(target);
    }
    this.currentWorldId = target;
    return target;
  }

  async handleWorldAction(action = {}) {
    const type = String(action.type || '').toLowerCase();

    if (type === 'create-world') {
      const worldId = action.worldId || createId('world');
      const created = this.worldManager.createWorld(worldId, {
        sensitivity: action.sensitivity || 'internal',
      });
      this.currentWorldId = worldId;
      return { type, world: created };
    }

    if (type === 'switch-world') {
      const worldId = action.worldId;
      if (!this.worldManager.hasWorld(worldId)) {
        throw new Error(`World "${worldId}" does not exist.`);
      }
      this.currentWorldId = worldId;
      return { type, world: this.worldManager.getWorld(worldId) };
    }

    if (type === 'snapshot') {
      const worldId = this.ensureWorld(action.worldId);
      const snapshot = this.worldManager.createSnapshot(worldId, { label: action.label || null });
      return { type, snapshot };
    }

    if (type === 'fork-world') {
      const forked = this.worldManager.forkWorld({
        fromWorldId: action.fromWorldId || this.ensureWorld(),
        fromSnapshotId: action.fromSnapshotId,
        newWorldId: action.newWorldId || createId('world'),
      });
      this.currentWorldId = forked.worldId;
      return { type, world: forked };
    }

    if (type === 'delete-world') {
      const worldId = action.worldId || this.currentWorldId;
      const deleted = this.worldManager.deleteWorld(worldId, {
        requireNoChildren: action.requireNoChildren !== false,
      });
      if (deleted.deleted && this.currentWorldId === worldId) {
        this.currentWorldId = null;
      }
      return { type, ...deleted };
    }

    throw new Error(`Unsupported world action "${action.type}".`);
  }

  async processTurn(input = {}) {
    const kind = String(input.kind || 'query').toLowerCase();
    if (kind === 'world-action') {
      return this.handleWorldAction(input.action || {});
    }

    if (kind === 'ingest') {
      return this._ingestTurn(input);
    }

    return this._queryTurn(input);
  }

  async _ingestTurn(input = {}) {
    if (!this.llmClient) {
      throw new Error('Ingest turn requires llmClient.');
    }

    const worldId = this.ensureWorld(input.worldId);
    const strategy = this.worldManager.getStrategy(worldId);
    const registryContext = this.worldManager.getRegistryContext(worldId, {
      strategy: input.registryContextStrategy || 'usage-topk',
      queryTerms: input.text || '',
      maxSymbols: input.registryContextLimit || 100,
    });

    const proposalId = input.proposalId || createId('fp_ingest');
    const encoded = await encodeFormalProposal({
      llmClient: this.llmClient,
      mode: input.mode || llmModeFromStrategy(strategy),
      worldId,
      proposalId,
      sourceId: input.sourceId || `source:${proposalId}`,
      text: input.text || '',
      logic: input.logic || 'QF_UF',
      source: input.source || {},
      tags: input.tags || [],
      registryContext,
    });

    if (!encoded.ok) {
      return {
        kind: 'ingest',
        ok: false,
        errors: encoded.errors,
        proposalId,
      };
    }

    const ingested = this.worldManager.ingestProposal(worldId, encoded.proposal);
    const promoted = this.worldManager.promoteProposalAsync
      ? await this.worldManager.promoteProposalAsync(worldId, proposalId)
      : this.worldManager.promoteProposal(worldId, proposalId);

    return {
      kind: 'ingest',
      ok: promoted.state === 'accepted',
      proposalId,
      ingest: ingested,
      promotion: promoted,
    };
  }

  async _queryTurn(input = {}) {
    if (!this.llmClient) {
      throw new Error('Query turn requires llmClient.');
    }
    throwIfAborted(input.abortSignal);

    const worldId = this.ensureWorld(input.worldId);
    const strategy = this.worldManager.getStrategy(worldId);
    const registrySelector = input.registryContextStrategy
      || (input.registryContext?.selector || 'usage-topk');

    const registryContext = this.worldManager.getRegistryContext(worldId, {
      strategy: registrySelector,
      queryTerms: input.text || '',
      maxSymbols: input.registryContextLimit || 120,
    });

    const queryProposalId = input.proposalId || createId('fp_query');
    const encodedQuery = await encodeQueryProposal({
      llmClient: this.llmClient,
      mode: input.mode || llmModeFromStrategy(strategy),
      worldId,
      proposalId: queryProposalId,
      question: input.text || '',
      logic: input.logic || 'QF_UF',
      registryContext,
    });
    throwIfAborted(input.abortSignal);

    if (!encodedQuery.ok) {
      return {
        kind: 'query',
        ok: false,
        stage: 'query-encoding',
        errors: encodedQuery.errors,
        rawText: encodedQuery.rawText || '',
        proposalId: queryProposalId,
      };
    }

    const fragments = this.worldManager
      .listFragments(worldId, { includeRestricted: false })
      .filter((fragment) => fragment.status === 'accepted');

    const intuition = createIntuitionStrategy({
      strategy: strategy.intuitionStrategy,
      representation: strategy.vsaRepresentation,
      dim: input.intuitionVectorDim || 256,
    });
    intuition.prepare({ worldId, fragments });
    const ownsSession = !input.sessionId;
    let sessionId = input.sessionId || null;
    const abortSignal = input.abortSignal || null;
    let abortListener = null;

    try {
      if (!sessionId) {
        sessionId = await this.solverAdapter.openSession({
          solver: solverFromStrategy(strategy),
          command: input.solverCommand,
          args: input.solverArgs,
          logic: encodedQuery.proposal.logic,
          timeoutMs: strategy.reasoningBudget.timeoutMs,
          maxMemoryMB: strategy.reasoningBudget.maxMemoryMB,
          timeoutOptionKey: input.timeoutOptionKey || null,
          memoryOptionKey: input.memoryOptionKey || null,
          setOptions: {
            'produce-models': true,
            'produce-unsat-cores': true,
          },
        });
      }
      throwIfAborted(abortSignal);

      if (abortSignal && sessionId) {
        abortListener = () => {
          this.solverAdapter.closeSession(sessionId).catch(() => {});
        };
        abortSignal.addEventListener('abort', abortListener, { once: true });
      }

      const reasoningInput = {
        solverAdapter: this.solverAdapter,
        sessionId,
        intuition,
        queryPlan: {
          ...encodedQuery.proposal.queryPlan,
          queryText: input.text || '',
        },
        fragments,
        registryEntries: this.worldManager.getRegistryEntries(worldId),
        budget: {
          ...strategy.reasoningBudget,
          ...(input.budget || {}),
        },
        llmAvailable: Boolean(this.llmClient),
        decoderPolicy: input.decoderPolicy || {},
        abortSignal,
      };

      let pipeline = await executeFormalQueryPipeline(reasoningInput);
      throwIfAborted(abortSignal);
      const recovered = pipeline.reasoning.rounds.some((round) => round.recovered === true);

      if (recovered) {
        if (this.onEvent) {
          this.onEvent({
            type: 'session-recovered-rerun',
            worldId,
            sessionId,
          });
        }
        pipeline = await executeFormalQueryPipeline(reasoningInput);
        pipeline.replayedAfterRecovery = true;
        throwIfAborted(abortSignal);
      }

      const decoded = await decodeResponse({
        reasoning: pipeline.reasoning,
        decisionContext: pipeline.response,
        llmClient: this.llmClient,
        useLLM: input.responseUseLLM === true,
        mode: input.mode || llmModeFromStrategy(strategy),
        policy: input.decoderPolicy || {},
      });
      throwIfAborted(abortSignal);

      return {
        kind: 'query',
        ok: true,
        worldId,
        sessionId,
        queryProposalId,
        reasoning: pipeline.reasoning,
        decision: pipeline.response,
        response: decoded,
        replayedAfterRecovery: pipeline.replayedAfterRecovery === true,
      };
    } finally {
      if (abortSignal && abortListener) {
        abortSignal.removeEventListener('abort', abortListener);
      }
      if (ownsSession && sessionId) {
        await this.solverAdapter.closeSession(sessionId).catch(() => {});
      }
    }
  }
}
