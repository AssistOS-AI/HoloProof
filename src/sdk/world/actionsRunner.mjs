import { ensureRecord } from './internalUtils.mjs';

export function executeWorldActions(manager, actions, options = {}) {
  if (!Array.isArray(actions)) {
    throw new Error('actions must be an array.');
  }

  let currentWorldId = options.currentWorldId || null;
  const captures = new Map();

  for (const action of actions) {
    ensureRecord(action, 'each action must be an object.');
    const params = action.params || {};
    ensureRecord(params, 'action.params must be an object.');

    switch (action.action) {
      case 'createWorld': {
        const result = manager.createWorld(params.worldId, {
          sensitivity: params.sensitivity,
        });
        currentWorldId = result.worldId;
        capture(action.captureAs, result.worldId, captures);
        break;
      }
      case 'setStrategy': {
        const worldId = resolveRef(params.worldId || currentWorldId, captures);
        manager.setStrategy(worldId, params);
        currentWorldId = worldId;
        break;
      }
      case 'setWorldPolicy': {
        const worldId = resolveRef(params.worldId || currentWorldId, captures);
        manager.setWorldPolicy(worldId, params);
        currentWorldId = worldId;
        break;
      }
      case 'ingestProposal': {
        const worldId = resolveRef(params.worldId || currentWorldId, captures);
        if (!params.formalProposal) {
          throw new Error('ingestProposal.params.formalProposal is required in SDK action execution.');
        }
        const result = manager.ingestProposal(worldId, params.formalProposal);
        capture(action.captureAs, result.proposalId, captures);
        currentWorldId = worldId;
        break;
      }
      case 'promoteProposal': {
        const worldId = resolveRef(params.worldId || currentWorldId, captures);
        const proposalId = resolveRef(params.proposalId, captures);
        const expectedRegistryVersion = Number.isInteger(params.expectedRegistryVersion)
          ? params.expectedRegistryVersion
          : undefined;
        manager.promoteProposal(worldId, proposalId, { expectedRegistryVersion });
        currentWorldId = worldId;
        break;
      }
      case 'snapshot': {
        const worldId = resolveRef(params.worldId || currentWorldId, captures);
        const result = manager.createSnapshot(worldId, { label: params.label || null });
        capture(action.captureAs, result.snapshotId, captures);
        currentWorldId = worldId;
        break;
      }
      case 'forkWorld': {
        const fromWorldId = resolveRef(params.fromWorldId, captures);
        const fromSnapshotId = resolveRef(params.fromSnapshotId, captures);
        const result = manager.forkWorld({
          fromWorldId,
          fromSnapshotId,
          newWorldId: params.newWorldId,
        });
        currentWorldId = result.worldId;
        capture(action.captureAs, result.worldId, captures);
        break;
      }
      case 'switchWorld': {
        currentWorldId = resolveRef(params.worldId, captures);
        manager._requireWorld(currentWorldId);
        break;
      }
      default:
        throw new Error(`Unknown world action "${action.action}".`);
    }
  }

  return {
    currentWorldId,
    captures: Object.fromEntries(captures.entries()),
  };
}

function capture(name, value, captures) {
  if (typeof name !== 'string' || !name.trim()) {
    return;
  }
  captures.set(name, value);
}

function resolveRef(value, captures) {
  if (typeof value !== 'string') {
    return value;
  }
  if (!value.startsWith('$')) {
    return value;
  }

  const key = value.slice(1);
  if (!captures.has(key)) {
    throw new Error(`Unresolved capture reference "$${key}".`);
  }

  return captures.get(key);
}
