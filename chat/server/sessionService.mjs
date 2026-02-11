import { randomUUID } from 'node:crypto';
import {
  ChatOrchestrator,
  WorldManager,
  createAchillesLLMClient,
  createSolverSessionAdapter,
} from '../../src/index.mjs';
import { nowIso, serverLog, errorMeta } from './logging.mjs';
import { broadcast, sendSseEvent } from './sse.mjs';
import {
  sanitizeSessionLabel,
  safeSavedId,
  readSavedSnapshot,
  writeSavedSnapshot,
  buildSessionSnapshot,
  listSavedSessions,
} from './sessionPersistence.mjs';
import {
  isAbortLike,
  isLikelyLlmError,
  normalizeAssistantTurn,
  buildLlmErrorPayload,
  buildRuntimeErrorPayload,
  buildCancelledPayload,
  buildEncodingErrorPayload,
  summarizeWorld,
} from './sessionPayloads.mjs';

function nextProposalId(session) {
  session.proposalCounter += 1;
  return `fp_srv_${String(session.proposalCounter).padStart(6, '0')}`;
}

function nextTurnId(session) {
  session.turnCounter += 1;
  return `turn_${String(session.turnCounter).padStart(6, '0')}`;
}

function buildKnowledgeSummary(scenario) {
  return scenario.knowledge.reduce((acc, item) => {
    acc.proposals += 1;
    acc.declarations += Array.isArray(item.declarations) ? item.declarations.length : 0;
    acc.assertions += Array.isArray(item.assertions) ? item.assertions.length : 0;
    return acc;
  }, {
    proposals: 0,
    declarations: 0,
    assertions: 0,
  });
}

function buildKnowledgePreview(scenario) {
  const preview = [];
  for (let i = 0; i < scenario.knowledge.length; i += 1) {
    const proposal = scenario.knowledge[i];
    const sourceId = proposal.source?.sourceId || `source_${i + 1}`;
    const declarations = Array.isArray(proposal.declarations) ? proposal.declarations.length : 0;
    const assertions = Array.isArray(proposal.assertions) ? proposal.assertions.length : 0;
    const sampleAssertionIds = (proposal.assertions || [])
      .slice(0, 3)
      .map((item) => item.assertionId)
      .filter(Boolean);

    const head = `${sourceId}: ${declarations} declarations, ${assertions} assertions`;
    const tail = sampleAssertionIds.length > 0 ? ` (${sampleAssertionIds.join(', ')})` : '';
    preview.push(`${head}${tail}`);
  }
  return preview;
}

function publicScenarios(scenarios) {
  return scenarios.map((scenario) => {
    const knowledgeSummary = buildKnowledgeSummary(scenario);
    const knowledgePreview = buildKnowledgePreview(scenario);
    const loadHint = `Loads ${knowledgeSummary.proposals} proposal(s), ${knowledgeSummary.assertions} assertion(s), ${knowledgeSummary.declarations} declaration(s).`;

    return {
      id: scenario.id,
      title: scenario.title,
      category: scenario.category,
      description: scenario.description,
      problemCount: scenario.problems.length,
      knowledgeSummary,
      knowledgePreview,
      loadHint,
      problems: scenario.problems.map((problem, index) => ({
        id: `${scenario.id}-q${index + 1}`,
        prompt: problem.prompt,
        formalTarget: problem.formalTarget,
        answerStyle: problem.simulatedResult?.interpretation || 'formal-answer',
        expectedAnswer: problem.simulatedResult?.answer || null,
      })),
    };
  });
}

function llmModeFromProfile(llmProfile = '') {
  const profile = String(llmProfile || '').toLowerCase();
  return profile.includes('deep') ? 'deep' : 'fast';
}

export function createSessionService({ saveDir, scenarios, strategyOptions }) {
  const sessions = new Map();
  let llmClientPromise = null;

  async function getServerLLMClient() {
    if (!llmClientPromise) {
      llmClientPromise = createAchillesLLMClient({
        agentName: 'HoloProof-Server',
      }).catch(() => null);
    }
    return llmClientPromise;
  }

  async function configureSessionRuntime(session, snapshot = null) {
    const worldManager = new WorldManager();
    const solverAdapter = createSolverSessionAdapter({
      onSessionEvent: (event) => {
        broadcast(session, 'solver-event', {
          at: nowIso(),
          ...event,
        });
      },
    });
    const llmClient = await getServerLLMClient();
    if (!llmClient) {
      throw new Error('AchillesAgentLib LLM is not configured on server. Chat runtime requires server-side LLM configuration.');
    }

    const defaultWorldId = snapshot?.currentWorldId || `world_${session.id.slice(0, 8)}`;
    const orchestrator = new ChatOrchestrator({
      worldManager,
      solverAdapter,
      llmClient,
      defaultWorldId,
      onEvent: (event) => {
        broadcast(session, 'orchestrator-event', {
          at: nowIso(),
          ...event,
        });
      },
    });

    if (snapshot && Array.isArray(snapshot.worlds) && snapshot.worlds.length > 0) {
      for (const worldDump of snapshot.worlds) {
        worldManager.importWorld(worldDump, { overwrite: true });
      }
      const activeWorldId = snapshot.currentWorldId || snapshot.worlds[0].worldId;
      orchestrator.currentWorldId = activeWorldId;
      if (!worldManager.hasWorld(activeWorldId)) {
        orchestrator.ensureWorld(activeWorldId);
      }
    } else {
      orchestrator.ensureWorld(defaultWorldId);
    }

    session.worldManager = worldManager;
    session.solverAdapter = solverAdapter;
    session.orchestrator = orchestrator;
    session.llmAvailable = Boolean(llmClient);
    session.history = Array.isArray(snapshot?.history) ? snapshot.history.slice() : [];
    session.feedback = Array.isArray(snapshot?.feedback) ? snapshot.feedback.slice() : [];
    session.proposalCounter = Number.isInteger(snapshot?.proposalCounter) ? snapshot.proposalCounter : 0;
    session.turnCounter = Number.isInteger(snapshot?.turnCounter) ? snapshot.turnCounter : 0;
    session.activeTurn = null;
  }

  async function createSession(options = {}) {
    const session = {
      id: randomUUID(),
      createdAt: nowIso(),
      label: sanitizeSessionLabel(options.label),
      sseClients: new Set(),
      worldManager: null,
      solverAdapter: null,
      orchestrator: null,
      llmAvailable: false,
      history: [],
      feedback: [],
      proposalCounter: 0,
      turnCounter: 0,
      activeTurn: null,
    };

    await configureSessionRuntime(session, options.snapshot || null);
    sessions.set(session.id, session);
    return session;
  }

  function sessionSummary(session) {
    const worldId = session.orchestrator.currentWorldId;
    const worldInfo = worldId && session.worldManager.hasWorld(worldId)
      ? session.worldManager.getWorld(worldId)
      : null;
    const strategy = worldId && session.worldManager.hasWorld(worldId)
      ? session.worldManager.getStrategy(worldId)
      : null;

    return {
      sessionId: session.id,
      createdAt: session.createdAt,
      label: session.label,
      currentWorldId: worldId,
      worldInfo,
      strategy,
      llmAvailable: session.llmAvailable,
      activeTurnId: session.activeTurn?.turnId || null,
    };
  }

  function requireSession(sessionId) {
    const session = sessions.get(sessionId);
    if (!session) {
      throw new Error(`Unknown session "${sessionId}".`);
    }
    return session;
  }

  async function loadScenarioKnowledge(session, scenarioId) {
    const scenario = scenarios.find((item) => item.id === scenarioId);
    if (!scenario) {
      throw new Error(`Unknown scenario "${scenarioId}".`);
    }

    const worldId = session.orchestrator.ensureWorld(session.orchestrator.currentWorldId);
    const loaded = [];

    for (const proposalTemplate of scenario.knowledge) {
      const proposal = JSON.parse(JSON.stringify(proposalTemplate));
      proposal.proposalId = nextProposalId(session);
      proposal.worldId = worldId;

      session.worldManager.ingestProposal(worldId, proposal);
      const promoted = await session.worldManager.promoteProposalAsync(worldId, proposal.proposalId);
      loaded.push({
        proposalId: proposal.proposalId,
        state: promoted.state,
        conflicts: promoted.conflicts,
        warnings: promoted.warnings,
      });
    }

    const worldInfo = session.worldManager.getWorld(worldId);
    const knowledgeSummary = buildKnowledgeSummary(scenario);
    const payload = {
      scenarioId,
      title: scenario.title,
      loadedCount: loaded.length,
      acceptedCount: loaded.filter((item) => item.state === 'accepted').length,
      loadHint: `Loaded ${knowledgeSummary.proposals} proposal(s), ${knowledgeSummary.assertions} assertion(s), ${knowledgeSummary.declarations} declaration(s) into world "${worldId}".`,
      knowledgePreview: buildKnowledgePreview(scenario),
      worldInfo,
    };

    session.history.push({
      role: 'system',
      type: 'scenario-loaded',
      at: nowIso(),
      payload,
    });

    broadcast(session, 'system', {
      text: `Loaded scenario "${scenario.title}" (${payload.acceptedCount}/${payload.loadedCount} accepted).`,
      payload,
    });
    broadcast(session, 'world-updated', {
      worldInfo,
      strategy: session.worldManager.getStrategy(worldId),
    });

    return payload;
  }

  async function runQuery(session, userText, turnId, abortSignal) {
    serverLog('info', 'Query received', {
      sessionId: session.id,
      turnId,
      worldId: session.orchestrator.currentWorldId,
      textPreview: userText.slice(0, 160),
    });

    let result = null;
    try {
      const worldId = session.orchestrator.currentWorldId;
      const strategy = session.worldManager.getStrategy(worldId);
      const mode = llmModeFromProfile(strategy?.llmProfile);
      result = await session.orchestrator.processTurn({
        kind: 'query',
        worldId,
        text: userText,
        turnId,
        abortSignal,
        mode,
      });
    } catch (error) {
      if (abortSignal?.aborted || isAbortLike(error)) {
        const cancelledPayload = buildCancelledPayload(userText, turnId);
        session.history.push({ role: 'assistant', turnId, at: nowIso(), payload: cancelledPayload });
        broadcast(session, 'assistant', cancelledPayload);
        return cancelledPayload;
      }

      const message = error instanceof Error ? error.message : 'Unhandled server runtime error.';
      const llmError = isLikelyLlmError(error);
      serverLog('error', 'Runtime error while processing query', {
        sessionId: session.id,
        turnId,
        worldId: session.orchestrator.currentWorldId,
        llmError,
        textPreview: userText.slice(0, 160),
        ...errorMeta(error),
      });
      const payload = llmError
        ? buildLlmErrorPayload(message, userText, turnId)
        : buildRuntimeErrorPayload(message, userText, turnId);

      if (llmError) {
        broadcast(session, 'system', {
          text: `LLM error detected: ${message}`,
          payload: {
            turnId,
            reason: 'llm-runtime-error',
            message,
          },
        });
      }

      session.history.push({ role: 'assistant', turnId, at: nowIso(), payload });
      broadcast(session, 'assistant', payload);
      return payload;
    }

    if (abortSignal?.aborted) {
      const cancelledPayload = buildCancelledPayload(userText, turnId);
      session.history.push({ role: 'assistant', turnId, at: nowIso(), payload: cancelledPayload });
      broadcast(session, 'assistant', cancelledPayload);
      return cancelledPayload;
    }

    if (!result.ok) {
      const errorPayload = buildEncodingErrorPayload(result, userText, turnId);
      serverLog('warn', 'Query encoding failed', {
        sessionId: session.id,
        turnId,
        worldId: session.orchestrator.currentWorldId,
        stage: result.stage || 'query-encoding',
        errors: errorPayload.errors,
      });
      session.history.push({ role: 'assistant', turnId, at: nowIso(), payload: errorPayload });
      broadcast(session, 'assistant', errorPayload);
      return errorPayload;
    }

    const payload = normalizeAssistantTurn(session, userText, result, turnId);
    serverLog('info', 'Query completed', {
      sessionId: session.id,
      turnId,
      worldId: payload.worldInfo?.worldId || session.orchestrator.currentWorldId,
      solverVerdict: payload.solverVerdict,
      queryVerdict: payload.queryVerdict,
      action: payload.action,
      reason: payload.reason,
    });

    session.history.push({ role: 'assistant', turnId, at: nowIso(), payload });
    broadcast(session, 'assistant', payload);
    broadcast(session, 'world-updated', {
      worldInfo: payload.worldInfo,
      strategy: payload.strategy,
    });
    return payload;
  }

  function startQuery(session, text) {
    const userText = String(text || '').trim();
    if (!userText) {
      throw new Error('Query text cannot be empty.');
    }
    if (session.activeTurn) {
      throw new Error('A query is already running. Stop it or wait for completion.');
    }

    const turnId = nextTurnId(session);
    const controller = new AbortController();

    session.history.push({ role: 'user', turnId, text: userText, at: nowIso() });

    session.activeTurn = {
      turnId,
      text: userText,
      startedAt: nowIso(),
      controller,
      promise: null,
    };

    broadcast(session, 'turn-started', {
      turnId,
      text: userText,
      at: nowIso(),
    });

    session.activeTurn.promise = runQuery(session, userText, turnId, controller.signal)
      .catch((error) => {
        serverLog('error', 'Unexpected uncaught query failure', {
          sessionId: session.id,
          turnId,
          ...errorMeta(error),
        });
      })
      .finally(() => {
        const active = session.activeTurn;
        if (active && active.turnId === turnId) {
          session.activeTurn = null;
        }
        broadcast(session, 'turn-finished', {
          turnId,
          at: nowIso(),
        });
      });

    return {
      accepted: true,
      turnId,
    };
  }

  function cancelQuery(session, turnId = null) {
    if (!session.activeTurn) {
      return { cancelled: false, reason: 'no-active-query' };
    }
    if (turnId && session.activeTurn.turnId !== turnId) {
      return {
        cancelled: false,
        reason: 'turn-id-mismatch',
        activeTurnId: session.activeTurn.turnId,
      };
    }

    const activeTurnId = session.activeTurn.turnId;
    if (!session.activeTurn.controller.signal.aborted) {
      session.activeTurn.controller.abort();
    }

    broadcast(session, 'turn-cancelled', {
      turnId: activeTurnId,
      at: nowIso(),
    });

    return { cancelled: true, turnId: activeTurnId };
  }

  function setStrategy(session, updates) {
    const worldId = session.orchestrator.currentWorldId;
    const strategy = session.worldManager.setStrategy(worldId, updates);
    return {
      worldInfo: session.worldManager.getWorld(worldId),
      strategy,
    };
  }

  async function saveSession(session, label = null) {
    const snapshot = buildSessionSnapshot(session, label);
    await writeSavedSnapshot(saveDir, snapshot);
    return {
      savedId: snapshot.savedId,
      label: snapshot.label,
      createdAt: snapshot.createdAt,
    };
  }

  async function restoreSession(session, savedId) {
    const snapshot = await readSavedSnapshot(saveDir, savedId);
    await configureSessionRuntime(session, snapshot);
    return {
      restored: true,
      session: sessionSummary(session),
      restoredFrom: savedId,
    };
  }

  function recordFeedback(session, payload = {}) {
    const vote = String(payload.vote || '').toLowerCase();
    if (!['up', 'down'].includes(vote)) {
      throw new Error('Feedback vote must be "up" or "down".');
    }

    const entry = {
      turnId: String(payload.turnId || ''),
      vote,
      note: typeof payload.note === 'string' ? payload.note.slice(0, 400) : null,
      at: nowIso(),
    };

    session.feedback.push(entry);
    session.history.push({ role: 'feedback', at: entry.at, payload: entry });

    return {
      saved: true,
      feedbackCount: session.feedback.length,
      entry,
    };
  }

  async function deleteSession(sessionId) {
    const session = requireSession(sessionId);

    if (session.activeTurn) {
      cancelQuery(session, session.activeTurn.turnId);
    }

    for (const client of session.sseClients) {
      try {
        sendSseEvent(client, 'system', { text: 'Session closed by server.' });
        client.end();
      } catch {
        // Ignore.
      }
    }
    session.sseClients.clear();
    sessions.delete(session.id);

    return { deleted: true, sessionId: session.id };
  }

  function connectSse(session, request, response) {
    response.writeHead(200, {
      'Content-Type': 'text/event-stream; charset=utf-8',
      'Cache-Control': 'no-cache, no-transform',
      Connection: 'keep-alive',
    });
    response.write(': connected\n\n');

    session.sseClients.add(response);
    sendSseEvent(response, 'session-ready', sessionSummary(session));

    const keepAlive = setInterval(() => {
      try {
        response.write(': ping\n\n');
      } catch {
        // Connection cleanup happens on close.
      }
    }, 25000);

    request.on('close', () => {
      clearInterval(keepAlive);
      session.sseClients.delete(response);
      serverLog('info', 'SSE disconnected', {
        sessionId: session.id,
        clientsAfter: session.sseClients.size,
      });
    });
  }

  return {
    strategyOptions,

    async ensureBootLlm() {
      const llmClient = await getServerLLMClient();
      return Boolean(llmClient);
    },

    activeSessionCount() {
      return sessions.size;
    },

    listPublicScenarios() {
      return publicScenarios(scenarios);
    },

    async createSessionFromSavedId({ label = null, savedId = null } = {}) {
      const normalizedSavedId = savedId ? safeSavedId(savedId) : null;
      const snapshot = normalizedSavedId ? await readSavedSnapshot(saveDir, normalizedSavedId) : null;
      const session = await createSession({ label, snapshot });
      return {
        session,
        restoredFrom: normalizedSavedId,
      };
    },

    requireSession,
    sessionSummary,
    connectSse,

    async listSavedSessions() {
      return listSavedSessions(saveDir);
    },

    async loadScenario(session, scenarioId) {
      return loadScenarioKnowledge(session, scenarioId);
    },

    startQuery(session, text) {
      return startQuery(session, text);
    },

    cancelQuery(session, turnId = null) {
      return cancelQuery(session, turnId);
    },

    setStrategy(session, updates) {
      return setStrategy(session, updates);
    },

    async saveSession(session, label = null) {
      return saveSession(session, label);
    },

    async restoreSession(session, savedId) {
      return restoreSession(session, safeSavedId(savedId));
    },

    recordFeedback(session, payload = {}) {
      return recordFeedback(session, payload);
    },

    async deleteSession(sessionId) {
      return deleteSession(sessionId);
    },

    summarizeWorld,
  };
}
