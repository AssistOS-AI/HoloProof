import path from 'node:path';
import { promises as fs } from 'node:fs';
import { nowIso } from './logging.mjs';

export function sanitizeSessionLabel(label) {
  const text = String(label || '').trim();
  if (!text) {
    return null;
  }
  return text.slice(0, 120);
}

export function safeSavedId(id) {
  const text = String(id || '').trim();
  if (!/^[A-Za-z0-9_-]+$/.test(text)) {
    throw new Error('Invalid savedId.');
  }
  return text;
}

export async function ensureSaveDir(saveDir) {
  await fs.mkdir(saveDir, { recursive: true });
}

function snapshotFilePath(saveDir, savedId) {
  return path.join(saveDir, `${safeSavedId(savedId)}.json`);
}

export async function readSavedSnapshot(saveDir, savedId) {
  await ensureSaveDir(saveDir);
  const text = await fs.readFile(snapshotFilePath(saveDir, savedId), 'utf8');
  const snapshot = JSON.parse(text);
  if (!snapshot || typeof snapshot !== 'object') {
    throw new Error(`Invalid saved session payload for "${savedId}".`);
  }
  if (snapshot.schemaVersion !== 'holoproof.chat-session.v1') {
    throw new Error(`Unsupported saved session schema for "${savedId}".`);
  }
  return snapshot;
}

export async function writeSavedSnapshot(saveDir, snapshot) {
  await ensureSaveDir(saveDir);
  const target = snapshotFilePath(saveDir, snapshot.savedId);
  await fs.writeFile(target, JSON.stringify(snapshot, null, 2), 'utf8');
  return target;
}

export function buildSessionSnapshot(session, label = null) {
  const worldIds = session.worldManager.listWorldIds();
  const worlds = worldIds.map((worldId) => session.worldManager.exportWorld(worldId));
  return {
    schemaVersion: 'holoproof.chat-session.v1',
    savedId: `save_${Date.now()}_${session.id.slice(0, 8)}`,
    label: sanitizeSessionLabel(label) || session.label || `Session ${session.id.slice(0, 8)}`,
    createdAt: nowIso(),
    sourceSessionId: session.id,
    currentWorldId: session.orchestrator.currentWorldId,
    proposalCounter: session.proposalCounter,
    turnCounter: session.turnCounter,
    worlds,
    history: session.history.slice(),
    feedback: session.feedback.slice(),
  };
}

export async function listSavedSessions(saveDir) {
  await ensureSaveDir(saveDir);
  const files = (await fs.readdir(saveDir))
    .filter((name) => name.endsWith('.json'))
    .sort((left, right) => right.localeCompare(left));

  const items = [];
  for (const fileName of files) {
    const fullPath = path.join(saveDir, fileName);
    try {
      const raw = await fs.readFile(fullPath, 'utf8');
      const parsed = JSON.parse(raw);
      items.push({
        savedId: parsed.savedId,
        label: parsed.label,
        createdAt: parsed.createdAt,
        sourceSessionId: parsed.sourceSessionId,
        currentWorldId: parsed.currentWorldId,
        worldCount: Array.isArray(parsed.worlds) ? parsed.worlds.length : 0,
      });
    } catch {
      // Ignore malformed snapshots.
    }
  }
  return items;
}
