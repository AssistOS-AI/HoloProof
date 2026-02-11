export function nowIso() {
  return new Date().toISOString();
}

export function serverLog(level, message, meta = null) {
  const stamp = nowIso();
  const payload = meta ? ` ${JSON.stringify(meta)}` : '';
  if (level === 'error') {
    console.error(`[chat-server][${stamp}] ${message}${payload}`);
    return;
  }
  if (level === 'warn') {
    console.warn(`[chat-server][${stamp}] ${message}${payload}`);
    return;
  }
  console.log(`[chat-server][${stamp}] ${message}${payload}`);
}

export function errorMeta(error) {
  if (!(error instanceof Error)) {
    return { message: String(error) };
  }
  return {
    name: error.name,
    message: error.message,
    stack: error.stack,
  };
}
