import { readJsonBody, parseSessionRoute, sendJson, sendNotFound } from './httpUtils.mjs';
import { serverLog } from './logging.mjs';

function pickStrategyUpdates(body = {}) {
  const updates = {};
  for (const key of ['smtStrategy', 'intuitionStrategy', 'vsaRepresentation', 'llmProfile']) {
    if (typeof body[key] === 'string' && body[key].trim()) {
      updates[key] = body[key].trim();
    }
  }
  return updates;
}

export function createApiRouter({ sessionService }) {
  return {
    async handleApi(request, response, url) {
      const { pathname } = url;

      if (request.method === 'GET' && pathname === '/api/health') {
        return sendJson(response, 200, {
          ok: true,
          now: new Date().toISOString(),
          activeSessions: sessionService.activeSessionCount(),
        });
      }

      if (request.method === 'GET' && pathname === '/api/strategies') {
        return sendJson(response, 200, {
          strategyOptions: sessionService.strategyOptions,
        });
      }

      if (request.method === 'GET' && pathname === '/api/scenarios') {
        return sendJson(response, 200, {
          scenarios: sessionService.listPublicScenarios(),
        });
      }

      if (request.method === 'POST' && pathname === '/api/session') {
        const body = await readJsonBody(request);
        const created = await sessionService.createSessionFromSavedId({
          label: body.label || null,
          savedId: body.savedId || null,
        });
        serverLog('info', 'Session created', {
          sessionId: created.session.id,
          restoredFrom: created.restoredFrom,
          label: created.session.label,
          worldId: created.session.orchestrator.currentWorldId,
        });

        return sendJson(response, 201, {
          session: sessionService.sessionSummary(created.session),
          strategyOptions: sessionService.strategyOptions,
          restoredFrom: created.restoredFrom,
        });
      }

      if (request.method === 'GET' && pathname === '/api/saved-sessions') {
        const saved = await sessionService.listSavedSessions();
        return sendJson(response, 200, { saved });
      }

      const sessionEventsId = parseSessionRoute(pathname, '/events$');
      if (request.method === 'GET' && sessionEventsId) {
        const session = sessionService.requireSession(sessionEventsId);
        serverLog('info', 'SSE connected', {
          sessionId: session.id,
          clientsBefore: session.sseClients.size,
        });
        sessionService.connectSse(session, request, response);
        return;
      }

      const sessionStateId = parseSessionRoute(pathname, '$');
      if (request.method === 'GET' && sessionStateId && pathname.startsWith('/api/sessions/')) {
        const session = sessionService.requireSession(sessionStateId);
        return sendJson(response, 200, {
          session: sessionService.sessionSummary(session),
          historySize: session.history.length,
        });
      }

      const sessionMessageId = parseSessionRoute(pathname, '/message$');
      if (request.method === 'POST' && sessionMessageId) {
        const session = sessionService.requireSession(sessionMessageId);
        const body = await readJsonBody(request);
        const started = sessionService.startQuery(session, body.text || '');
        return sendJson(response, 202, {
          accepted: true,
          sessionId: session.id,
          turnId: started.turnId,
        });
      }

      const sessionCancelId = parseSessionRoute(pathname, '/cancel$');
      if (request.method === 'POST' && sessionCancelId) {
        const session = sessionService.requireSession(sessionCancelId);
        const body = await readJsonBody(request);
        const cancelled = sessionService.cancelQuery(session, body.turnId || null);
        return sendJson(response, 200, cancelled);
      }

      const sessionFeedbackId = parseSessionRoute(pathname, '/feedback$');
      if (request.method === 'POST' && sessionFeedbackId) {
        const session = sessionService.requireSession(sessionFeedbackId);
        const body = await readJsonBody(request);
        const saved = sessionService.recordFeedback(session, body);
        return sendJson(response, 201, saved);
      }

      const sessionStrategyId = parseSessionRoute(pathname, '/strategy$');
      if (request.method === 'POST' && sessionStrategyId) {
        const session = sessionService.requireSession(sessionStrategyId);
        const body = await readJsonBody(request);
        const updates = pickStrategyUpdates(body);

        if (Object.keys(updates).length === 0) {
          throw new Error('No valid strategy keys were provided.');
        }

        const payload = sessionService.setStrategy(session, updates);
        for (const client of session.sseClients) {
          try {
            client.write(`event: strategy-updated\ndata: ${JSON.stringify(payload)}\n\n`);
          } catch {
            // Ignore stale SSE connections.
          }
        }
        return sendJson(response, 200, payload);
      }

      const sessionScenarioId = parseSessionRoute(pathname, '/load-scenario$');
      if (request.method === 'POST' && sessionScenarioId) {
        const session = sessionService.requireSession(sessionScenarioId);
        const body = await readJsonBody(request);
        const result = await sessionService.loadScenario(session, body.scenarioId);
        serverLog('info', 'Scenario loaded', {
          sessionId: session.id,
          scenarioId: body.scenarioId,
          acceptedCount: result.acceptedCount,
          loadedCount: result.loadedCount,
        });
        return sendJson(response, 200, result);
      }

      const sessionSaveId = parseSessionRoute(pathname, '/save$');
      if (request.method === 'POST' && sessionSaveId) {
        const session = sessionService.requireSession(sessionSaveId);
        const body = await readJsonBody(request);
        const saved = await sessionService.saveSession(session, body.label || null);
        serverLog('info', 'Session saved', {
          sessionId: session.id,
          savedId: saved.savedId,
        });
        return sendJson(response, 201, saved);
      }

      const sessionRestoreId = parseSessionRoute(pathname, '/restore$');
      if (request.method === 'POST' && sessionRestoreId) {
        const session = sessionService.requireSession(sessionRestoreId);
        const body = await readJsonBody(request);
        const restored = await sessionService.restoreSession(session, body.savedId);
        serverLog('info', 'Session restored', {
          sessionId: session.id,
          restoredFrom: restored.restoredFrom,
          worldId: restored.session.currentWorldId,
        });

        for (const client of session.sseClients) {
          try {
            client.write(`event: system\ndata: ${JSON.stringify({
              text: `Restored snapshot "${body.savedId}".`,
              payload: { savedId: body.savedId },
            })}\n\n`);
            client.write(`event: world-updated\ndata: ${JSON.stringify({
              worldInfo: restored.session.worldInfo,
              strategy: restored.session.strategy,
            })}\n\n`);
          } catch {
            // Ignore stale SSE clients.
          }
        }

        return sendJson(response, 200, restored);
      }

      const sessionDeleteId = parseSessionRoute(pathname, '$');
      if (request.method === 'DELETE' && sessionDeleteId && pathname.startsWith('/api/sessions/')) {
        const deleted = await sessionService.deleteSession(sessionDeleteId);
        serverLog('info', 'Session deleted', {
          sessionId: deleted.sessionId,
        });
        return sendJson(response, 200, deleted);
      }

      if (pathname.startsWith('/api/')) {
        serverLog('warn', 'API route not found', {
          method: request.method,
          pathname,
        });
      }
      return sendNotFound(response);
    },
  };
}
