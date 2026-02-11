import { promises as fs } from 'node:fs';
import path from 'node:path';

function safeWorldId(worldId) {
  const id = String(worldId || '').trim();
  if (!id) {
    throw new Error('worldId must be a non-empty string.');
  }
  if (!/^[A-Za-z0-9_-]+$/.test(id)) {
    throw new Error(`Invalid worldId "${worldId}" for file persistence.`);
  }
  return id;
}

export class JsonFilePersistenceAdapter {
  constructor(options = {}) {
    this.baseDir = options.baseDir || 'data/worlds';
  }

  worldPath(worldId) {
    return path.join(this.baseDir, `${safeWorldId(worldId)}.json`);
  }

  async ensureBaseDir() {
    await fs.mkdir(this.baseDir, { recursive: true });
  }

  async saveWorld(serializedWorld) {
    if (!serializedWorld || typeof serializedWorld !== 'object') {
      throw new Error('saveWorld requires serialized world object.');
    }
    const worldId = safeWorldId(serializedWorld.worldId);
    await this.ensureBaseDir();
    const target = this.worldPath(worldId);
    await fs.writeFile(target, JSON.stringify(serializedWorld, null, 2), 'utf8');
    return { worldId, path: target };
  }

  async loadWorld(worldId) {
    const target = this.worldPath(worldId);
    const text = await fs.readFile(target, 'utf8');
    const parsed = JSON.parse(text);
    if (!parsed || typeof parsed !== 'object') {
      throw new Error(`Invalid persisted world payload at ${target}.`);
    }
    return parsed;
  }

  async deleteWorld(worldId) {
    const target = this.worldPath(worldId);
    try {
      await fs.unlink(target);
      return { deleted: true };
    } catch (error) {
      if (error && error.code === 'ENOENT') {
        return { deleted: false };
      }
      throw error;
    }
  }

  async listWorldIds() {
    await this.ensureBaseDir();
    const names = await fs.readdir(this.baseDir);
    return names
      .filter((name) => name.endsWith('.json'))
      .map((name) => name.slice(0, -'.json'.length))
      .sort((left, right) => left.localeCompare(right));
  }
}

export async function persistWorldManagerWorld(worldManager, worldId, adapter) {
  if (!worldManager || typeof worldManager.exportWorld !== 'function') {
    throw new Error('persistWorldManagerWorld requires worldManager.exportWorld().');
  }
  if (!adapter || typeof adapter.saveWorld !== 'function') {
    throw new Error('persistWorldManagerWorld requires adapter.saveWorld().');
  }

  const exported = worldManager.exportWorld(worldId);
  return adapter.saveWorld(exported);
}

export async function loadWorldIntoManager(worldManager, worldId, adapter, options = {}) {
  if (!worldManager || typeof worldManager.importWorld !== 'function') {
    throw new Error('loadWorldIntoManager requires worldManager.importWorld().');
  }
  if (!adapter || typeof adapter.loadWorld !== 'function') {
    throw new Error('loadWorldIntoManager requires adapter.loadWorld().');
  }

  const serialized = await adapter.loadWorld(worldId);
  return worldManager.importWorld(serialized, options);
}
