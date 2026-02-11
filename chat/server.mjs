import http from 'node:http';
import { randomUUID } from 'node:crypto';
import { DEMO_SCENARIOS } from './demo-scenarios.mjs';
import { CHAT_DIR, CONTENT_TYPES, HOST, PORT, SAVE_DIR, STRATEGY_OPTIONS } from './server/config.mjs';
import { createSessionService } from './server/sessionService.mjs';
import { createApiRouter } from './server/apiRouter.mjs';
import { serveStatic } from './server/staticHandler.mjs';
import { errorMeta, serverLog } from './server/logging.mjs';
import { sendJson } from './server/httpUtils.mjs';

const sessionService = createSessionService({
  saveDir: SAVE_DIR,
  scenarios: DEMO_SCENARIOS,
  strategyOptions: STRATEGY_OPTIONS,
});

const llmReady = await sessionService.ensureBootLlm();
if (!llmReady) {
  console.error('[chat-server] AchillesAgentLib LLM is not configured. Refusing to start.');
  process.exit(1);
}

const apiRouter = createApiRouter({ sessionService });

const server = http.createServer(async (request, response) => {
  const requestId = randomUUID().slice(0, 8);
  const startedAt = Date.now();
  const method = request.method || 'GET';
  const rawUrl = request.url || '/';

  response.setHeader('X-Request-Id', requestId);
  response.on('finish', () => {
    serverLog('info', 'HTTP request completed', {
      requestId,
      method,
      url: rawUrl,
      statusCode: response.statusCode,
      elapsedMs: Date.now() - startedAt,
    });
  });

  try {
    const url = new URL(request.url || '/', `http://${request.headers.host || 'localhost'}`);
    if (url.pathname.startsWith('/api/')) {
      return await apiRouter.handleApi(request, response, url);
    }

    return await serveStatic({
      response,
      pathname: url.pathname,
      chatDir: CHAT_DIR,
      contentTypes: CONTENT_TYPES,
    });
  } catch (error) {
    const message = error instanceof Error ? error.message : 'Internal server error.';
    serverLog('error', 'Unhandled HTTP handler error', {
      requestId,
      method,
      url: rawUrl,
      ...errorMeta(error),
    });
    return sendJson(response, 500, { error: message });
  }
});

server.listen(PORT, HOST, () => {
  serverLog('info', `Running on http://${HOST}:${PORT}`);
  serverLog('info', 'No client-side API keys are required; all LLM access stays server-side.');
});
