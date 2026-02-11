export function sendSseEvent(response, eventName, payload) {
  response.write(`event: ${eventName}\n`);
  response.write(`data: ${JSON.stringify(payload)}\n\n`);
}

export function broadcast(session, eventName, payload) {
  for (const response of session.sseClients) {
    try {
      sendSseEvent(response, eventName, payload);
    } catch {
      // Connection cleanup happens on close handlers.
    }
  }
}
