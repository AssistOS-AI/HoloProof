export function sendJson(response, statusCode, payload) {
  response.writeHead(statusCode, {
    'Content-Type': 'application/json; charset=utf-8',
    'Cache-Control': 'no-store',
  });
  response.end(JSON.stringify(payload));
}

export function sendNotFound(response, message = 'Not found') {
  sendJson(response, 404, { error: message });
}

export async function readJsonBody(request) {
  const chunks = [];
  let size = 0;

  for await (const chunk of request) {
    size += chunk.length;
    if (size > 2 * 1024 * 1024) {
      throw new Error('Request body too large.');
    }
    chunks.push(chunk);
  }

  if (chunks.length === 0) {
    return {};
  }

  const raw = Buffer.concat(chunks).toString('utf8').trim();
  if (!raw) {
    return {};
  }

  try {
    return JSON.parse(raw);
  } catch {
    throw new Error('Invalid JSON request body.');
  }
}

export function parseSessionRoute(pathname, suffix = '') {
  const re = new RegExp(`^/api/sessions/([^/]+)${suffix}$`);
  const match = pathname.match(re);
  if (!match) {
    return null;
  }
  return decodeURIComponent(match[1]);
}
