export function isAbortLike(error) {
  if (error?.name === 'AbortError') {
    return true;
  }
  const message = String(error?.message || '').toLowerCase();
  return message.includes('cancel') || message.includes('aborted');
}

export function isLikelyLlmError(error) {
  const text = String(error?.message || error || '').toLowerCase();
  const keys = [
    'llm',
    'achilles',
    'model',
    'api key',
    'apikey',
    'unauthorized',
    'forbidden',
    'rate limit',
    'provider',
    'openai',
    'anthropic',
    'gemini',
  ];
  return keys.some((key) => text.includes(key));
}

export function buildReasoningTrace(turn) {
  const lines = [];
  const reasoning = turn.reasoning || {};
  const decision = turn.decision?.decision || turn.decision || {};
  lines.push(`Verification mode: ${reasoning.verificationMode || 'unknown'}`);
  lines.push(`Solver verdict: ${reasoning.solverVerdict || 'unknown'}`);
  lines.push(`Query verdict: ${reasoning.queryVerdict || 'unknown'}`);
  lines.push(`Response action: ${decision.action || turn.response?.action || 'answer'}`);
  lines.push(`Total time: ${Number(reasoning.totalElapsedMs || 0).toFixed(2)} ms`);

  if (Array.isArray(reasoning.rounds) && reasoning.rounds.length > 0) {
    lines.push(`Rounds: ${reasoning.rounds.length}`);
    for (const round of reasoning.rounds) {
      lines.push(
        `- round ${round.round}: solver=${round.solverVerdict}, active=${round.activeCount}, elapsed=${Number(round.elapsedMs || 0).toFixed(2)}ms`,
      );
    }
  }

  if (reasoning.complexityGuard && reasoning.complexityGuard.ok === false) {
    lines.push(`Complexity guard: blocked (${reasoning.complexityGuard.violations.join('; ')})`);
  }

  if (reasoning.knowledgeGaps?.hasGaps) {
    lines.push(`Knowledge gaps: ${reasoning.knowledgeGaps.missingEvidence.length}`);
  }

  return lines.join('\n');
}

export function normalizeAssistantTurn(session, userText, turn, turnId) {
  const worldId = turn.worldId || session.orchestrator.currentWorldId;
  const worldInfo = worldId && session.worldManager.hasWorld(worldId)
    ? session.worldManager.getWorld(worldId)
    : null;
  const strategy = worldId && session.worldManager.hasWorld(worldId)
    ? session.worldManager.getStrategy(worldId)
    : null;

  return {
    type: 'query-result',
    turnId,
    userQuery: userText,
    answerText: turn.response?.message || 'No answer text returned.',
    action: turn.response?.action || turn.decision?.decision?.action || 'answer',
    reason: turn.response?.reason || turn.decision?.decision?.reason || null,
    solverVerdict: turn.reasoning?.solverVerdict || 'unknown',
    queryVerdict: turn.reasoning?.queryVerdict || 'unknown',
    reasoningTrace: buildReasoningTrace(turn),
    surfacedIssues: turn.response?.surfacedIssues || [],
    followupQuestions: turn.response?.questions || [],
    evidenceAnchors: turn.response?.evidenceAnchors || [],
    worldInfo,
    strategy,
    replayedAfterRecovery: turn.replayedAfterRecovery === true,
    technical: {
      reasoning: turn.reasoning || null,
      decision: turn.decision || null,
      response: turn.response || null,
    },
  };
}

export function buildRuntimeErrorPayload(message, userText, turnId) {
  return {
    type: 'runtime-error',
    turnId,
    userQuery: userText,
    answerText: 'Server runtime failed while processing your query.',
    action: 'ask-user',
    reason: 'runtime-error',
    solverVerdict: 'error',
    queryVerdict: 'error',
    reasoningTrace: `Runtime error:\n- ${message}`,
    errors: [message],
    surfacedIssues: [
      {
        code: 'runtime-error',
        level: 'error',
        message,
      },
    ],
    followupQuestions: [
      'Please retry the query.',
      'If the error persists, inspect server logs for stack trace.',
    ],
    evidenceAnchors: [],
  };
}

export function buildLlmErrorPayload(message, userText, turnId) {
  return {
    type: 'llm-error',
    turnId,
    userQuery: userText,
    answerText: 'LLM request failed. Check server-side LLM configuration and provider status.',
    action: 'ask-user',
    reason: 'llm-runtime-error',
    solverVerdict: 'error',
    queryVerdict: 'error',
    reasoningTrace: `LLM stage failed:\\n- ${message}`,
    errors: [message],
    surfacedIssues: [
      {
        code: 'llm-runtime-error',
        level: 'error',
        message,
      },
    ],
    followupQuestions: [
      'Verify AchillesAgentLib model/provider config on server.',
      'Retry after confirming API key and selected model profile.',
    ],
    evidenceAnchors: [],
  };
}

export function buildCancelledPayload(userText, turnId) {
  return {
    type: 'query-cancelled',
    turnId,
    userQuery: userText,
    answerText: 'Query was cancelled before completion.',
    action: 'cancelled',
    reason: 'user-cancelled',
    solverVerdict: 'cancelled',
    queryVerdict: 'cancelled',
    reasoningTrace: 'Execution was interrupted by user request.',
    errors: [],
    surfacedIssues: [
      {
        code: 'query-cancelled',
        level: 'warning',
        message: 'The running query was cancelled.',
      },
    ],
    followupQuestions: [],
    evidenceAnchors: [],
  };
}

export function buildEncodingErrorPayload(result, userText, turnId) {
  const errors = Array.isArray(result.errors) ? result.errors : ['Query could not be encoded.'];
  const payload = {
    type: 'query-error',
    turnId,
    userQuery: userText,
    answerText: 'Query could not be formalized by server-side encoder.',
    action: 'ask-user',
    reason: 'query-encoding-failed',
    solverVerdict: 'error',
    queryVerdict: 'error',
    reasoningTrace: `Encoding stage: ${result.stage || 'query-encoding'}\n\nErrors:\n- ${errors.join('\n- ')}`,
    errors,
    surfacedIssues: [
      {
        code: 'query-encoding-failed',
        level: 'error',
        message: errors[0],
      },
    ],
    followupQuestions: [
      'Can you restate the question in shorter, explicit terms?',
      'If you are using demo data, load the matching scenario first.',
    ],
    evidenceAnchors: [],
  };

  if (typeof result.rawText === 'string' && result.rawText.trim()) {
    payload.rawEncoderText = result.rawText.slice(0, 1200);
  }

  return payload;
}

export function summarizeWorld(world) {
  if (!world) {
    return null;
  }
  return {
    worldId: world.worldId,
    registryVersion: world.registryVersion,
    fragmentCount: world.fragmentCount,
    proposalCount: world.proposalCount,
  };
}
