import { SymbolRegistry } from '../symbolRegistry.mjs';
import { deepClone, ensureRecord, normalizeSensitivity, nowIso } from './internalUtils.mjs';

export function createEmptyWorld({
  worldId,
  now,
  parentWorldId,
  parentSnapshotId,
  sensitivity,
  tracePolicy,
}) {
  return {
    worldId,
    parentWorldId,
    parentSnapshotId,
    createdAt: nowIso(now),
    registryVersion: 0,
    strategy: {
      smtStrategy: 'smt-z3-incremental-refutation',
      intuitionStrategy: 'no-intuition',
      vsaRepresentation: 'vsa-disabled',
      llmProfile: 'llm-cached',
      reasoningBudget: {
        timeoutMs: 4000,
        maxActiveAtoms: 400,
        maxExpansionRounds: 3,
        expansionStep: 50,
        maxMemoryMB: 512,
      },
    },
    securityPolicy: {
      sensitivity: normalizeSensitivity(sensitivity),
      traceRetentionDays: Number.isInteger(tracePolicy?.traceRetentionDays) ? tracePolicy.traceRetentionDays : 30,
      redactModelValues: tracePolicy?.redactModelValues === true,
      allowUnsatCoreDetails: tracePolicy?.allowUnsatCoreDetails === true,
      comparisonVisibility: tracePolicy?.comparisonVisibility || 'fragment-ids',
    },
    symbolRegistry: new SymbolRegistry(),
    proposals: new Map(),
    fragments: new Map(),
    snapshots: new Map(),
    snapshotOrder: [],
    counters: {
      snapshot: 0,
      fragment: 0,
    },
  };
}

export function hydrateWorldFromSnapshot(world, snapshot) {
  world.strategy = deepClone(snapshot.strategy || world.strategy);
  world.securityPolicy = deepClone(snapshot.securityPolicy || world.securityPolicy);
  world.registryVersion = Number.isInteger(snapshot.registryVersion) ? snapshot.registryVersion : 0;
  world.symbolRegistry = new SymbolRegistry(snapshot.registryEntries || [], {
    sortAliases: snapshot.registrySortAliases || [],
  });

  for (const proposal of snapshot.proposals || []) {
    world.proposals.set(proposal.proposalId, deepClone(proposal));
  }

  for (const fragment of snapshot.fragments || []) {
    world.fragments.set(fragment.fragmentId, deepClone(fragment));
  }

  if (snapshot.counters) {
    world.counters = deepClone(snapshot.counters);
  }
}

export function summarizeWorld(world) {
  return {
    worldId: world.worldId,
    parentWorldId: world.parentWorldId,
    parentSnapshotId: world.parentSnapshotId,
    createdAt: world.createdAt,
    registryVersion: world.registryVersion,
    strategy: deepClone(world.strategy),
    securityPolicy: deepClone(world.securityPolicy),
    proposalCount: world.proposals.size,
    fragmentCount: world.fragments.size,
    snapshotCount: world.snapshots.size,
  };
}

export function createSnapshotRecord(worldId, world, nowFn, options = {}) {
  world.counters.snapshot += 1;
  const snapshotId = `snap_${String(world.counters.snapshot).padStart(4, '0')}`;
  const snapshot = {
    snapshotId,
    worldId,
    label: options.label || null,
    createdAt: nowIso(nowFn),
    registryVersion: world.registryVersion,
    strategy: deepClone(world.strategy),
    securityPolicy: deepClone(world.securityPolicy),
    registryEntries: world.symbolRegistry.listEntries(),
    registrySortAliases: world.symbolRegistry.listSortAliases(),
    proposals: [...world.proposals.values()].map((record) => deepClone(record)),
    fragments: [...world.fragments.values()].map((fragment) => deepClone(fragment)),
    counters: deepClone(world.counters),
  };

  world.snapshots.set(snapshotId, snapshot);
  world.snapshotOrder.push(snapshotId);
  return deepClone(snapshot);
}

export function exportSerializedWorld(world) {
  return {
    worldId: world.worldId,
    parentWorldId: world.parentWorldId,
    parentSnapshotId: world.parentSnapshotId,
    createdAt: world.createdAt,
    registryVersion: world.registryVersion,
    strategy: deepClone(world.strategy),
    securityPolicy: deepClone(world.securityPolicy),
    registryEntries: world.symbolRegistry.listEntries(),
    registrySortAliases: world.symbolRegistry.listSortAliases(),
    proposals: [...world.proposals.values()].map((record) => deepClone(record)),
    fragments: [...world.fragments.values()].map((fragment) => deepClone(fragment)),
    snapshots: [...world.snapshots.values()].map((snapshot) => deepClone(snapshot)),
    snapshotOrder: world.snapshotOrder.slice(),
    counters: deepClone(world.counters),
  };
}

export function importSerializedWorld(serializedWorld, options = {}) {
  ensureRecord(serializedWorld, 'serializedWorld must be an object.');
  const worldId = serializedWorld.worldId;
  if (typeof worldId !== 'string' || !worldId.trim()) {
    throw new Error('serializedWorld.worldId must be a non-empty string.');
  }

  const nowFn = options.now;
  const world = createEmptyWorld({
    worldId,
    now: nowFn,
    parentWorldId: serializedWorld.parentWorldId || null,
    parentSnapshotId: serializedWorld.parentSnapshotId || null,
    sensitivity: serializedWorld.securityPolicy?.sensitivity || 'internal',
    tracePolicy: serializedWorld.securityPolicy || {},
  });

  world.createdAt = serializedWorld.createdAt || world.createdAt;
  world.registryVersion = Number.isInteger(serializedWorld.registryVersion) ? serializedWorld.registryVersion : 0;
  world.strategy = deepClone(serializedWorld.strategy || world.strategy);
  world.securityPolicy = deepClone(serializedWorld.securityPolicy || world.securityPolicy);
  world.symbolRegistry = new SymbolRegistry(serializedWorld.registryEntries || [], {
    sortAliases: serializedWorld.registrySortAliases || [],
  });

  for (const record of serializedWorld.proposals || []) {
    world.proposals.set(record.proposalId, deepClone(record));
  }

  for (const fragment of serializedWorld.fragments || []) {
    world.fragments.set(fragment.fragmentId, deepClone(fragment));
  }

  for (const snapshot of serializedWorld.snapshots || []) {
    world.snapshots.set(snapshot.snapshotId, deepClone(snapshot));
  }

  world.snapshotOrder = Array.isArray(serializedWorld.snapshotOrder)
    ? serializedWorld.snapshotOrder.slice()
    : [...world.snapshots.keys()].sort();

  if (serializedWorld.counters) {
    world.counters = deepClone(serializedWorld.counters);
  }

  return {
    worldId,
    world,
  };
}
