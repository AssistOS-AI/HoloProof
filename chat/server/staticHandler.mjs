import path from 'node:path';
import { promises as fs } from 'node:fs';
import { sendNotFound } from './httpUtils.mjs';
import { serverLog } from './logging.mjs';

export async function serveStatic({ response, pathname, chatDir, contentTypes }) {
  if (pathname === '/favicon.ico') {
    response.writeHead(204);
    response.end();
    return;
  }

  const relativePath = pathname === '/' ? '/index.html' : pathname;
  const safePath = path.normalize(relativePath).replace(/^(\.\.(\/|\\|$))+/, '');
  const resolved = path.resolve(chatDir, `.${safePath}`);

  if (!resolved.startsWith(chatDir)) {
    return sendNotFound(response, 'Invalid path.');
  }

  try {
    const stat = await fs.stat(resolved);
    if (stat.isDirectory()) {
      return sendNotFound(response);
    }

    const ext = path.extname(resolved).toLowerCase();
    const type = contentTypes[ext] || 'application/octet-stream';
    const content = await fs.readFile(resolved);
    response.writeHead(200, {
      'Content-Type': type,
      'Cache-Control': 'no-store',
    });
    response.end(content);
  } catch (error) {
    serverLog('warn', 'Static file not found', {
      pathname,
      resolved,
      error: error instanceof Error ? error.message : String(error),
    });
    sendNotFound(response);
  }
}
