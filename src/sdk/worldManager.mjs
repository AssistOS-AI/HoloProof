import { collectReferencedSymbols, validateFormalProposal } from './formalProposal.mjs';
import { SymbolRegistry } from './symbolRegistry.mjs';

function deepClone(value) {
  return JSON.parse(JSON.stringify(value));
}

function nowIso(nowFn) {
  return new Date(nowFn()).toISOString();
}

function ensureRecord(value, message) {
  if (value === null || typeof value !== 'object' || Array.isArray(value)) {
    throw new Error(message);
  }
}

function normalizeSensitivity(value) {
  const allowed = new Set(['public', 'internal', 'confidential', 'restricted']);
  if (typeof value !== 'string') {
    return 'internal';
  }
  const normalized = value.toLowerCase();
  return allowed.has(normalized) ? normalized : 'internal';
}

export class WorldManager {
  constructor(options = {}) {
    this._worlds = new Map();
    this._now = typeof options.now === 'function' ? options.now : Date.now;
  }

  createWorld(worldId, options = {}) {
    if (this._worlds.has(worldId)) {
      throw new Error(`World "${worldId}" already exists.`);
    }

    const snapshot = options.fromSnapshot || null;
    const world = createEmptyWorld({
      worldId,
      now: this._now,
      parentWorldId: options.parentWorldId || null,
      parentSnapshotId: options.parentSnapshotId || null,
      sensitivity: options.sensitivity,
      tracePolicy: options.tracePolicy,
    });

    if (snapshot) {
      hydrateWorldFromSnapshot(world, snapshot);
    }

    this._worlds.set(worldId, world);
    return this.getWorld(worldId);
  }

  hasWorld(worldId) {
    return this._worlds.has(worldId);
  }

  getWorld(worldId) {
    const world = this._worlds.get(worldId);
    if (!world) {
      throw new Error(`World "${worldId}" does not exist.`);
    }

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

  setStrategy(worldId, strategy) {
    const world = this._requireWorld(worldId);
    ensureRecord(strategy, 'strategy must be an object.');

    world.strategy = {
      smtStrategy: strategy.smtStrategy || world.strategy.smtStrategy,
      intuitionStrategy: strategy.intuitionStrategy || world.strategy.intuitionStrategy,
      vsaRepresentation: strategy.vsaRepresentation || world.strategy.vsaRepresentation,
      llmProfile: strategy.llmProfile || world.strategy.llmProfile,
      reasoningBudget: {
        timeoutMs: Number.isInteger(strategy.timeoutMs) ? strategy.timeoutMs : world.strategy.reasoningBudget.timeoutMs,
        maxActiveAtoms: Number.isInteger(strategy.maxActiveAtoms)
          ? strategy.maxActiveAtoms
          : world.strategy.reasoningBudget.maxActiveAtoms,
        maxExpansionRounds: Number.isInteger(strategy.maxExpansionRounds)
          ? strategy.maxExpansionRounds
          : world.strategy.reasoningBudget.maxExpansionRounds,
        expansionStep: Number.isInteger(strategy.expansionStep)
          ? strategy.expansionStep
          : world.strategy.reasoningBudget.expansionStep,
        maxMemoryMB: Number.isInteger(strategy.maxMemoryMB)
          ? strategy.maxMemoryMB
          : world.strategy.reasoningBudget.maxMemoryMB,
      },
    };

    return deepClone(world.strategy);
  }

  setWorldPolicy(worldId, policy) {
    const world = this._requireWorld(worldId);
    ensureRecord(policy, 'policy must be an object.');

    const current = world.securityPolicy;
    world.securityPolicy = {
      sensitivity: normalizeSensitivity(policy.sensitivity || current.sensitivity),
      traceRetentionDays: Number.isInteger(policy.traceRetentionDays)
        ? policy.traceRetentionDays
        : current.traceRetentionDays,
      redactModelValues: typeof policy.redactModelValues === 'boolean'
        ? policy.redactModelValues
        : current.redactModelValues,
      allowUnsatCoreDetails: typeof policy.allowUnsatCoreDetails === 'boolean'
        ? policy.allowUnsatCoreDetails
        : current.allowUnsatCoreDetails,
      comparisonVisibility: policy.comparisonVisibility || current.comparisonVisibility,
    };

    return deepClone(world.securityPolicy);
  }

  getWorldPolicy(worldId) {
    const world = this._requireWorld(worldId);
    return deepClone(world.securityPolicy);
  }

  ingestProposal(worldId, proposal) {
    const world = this._requireWorld(worldId);
    ensureRecord(proposal, 'proposal must be an object.');

    const proposalId = proposal.proposalId;
    if (typeof proposalId !== 'string' || !proposalId.trim()) {
      throw new Error('proposal.proposalId must be a non-empty string.');
    }

    if (world.proposals.has(proposalId)) {
      throw new Error(`Proposal "${proposalId}" already exists in world "${worldId}".`);
    }

    const timestamp = nowIso(this._now);
    const record = {
      proposalId,
      proposal: deepClone(proposal),
      state: 'proposed',
      createdAt: timestamp,
      updatedAt: timestamp,
      registrySnapshotId: null,
      ingestedRegistryVersion: world.registryVersion,
      validationErrors: [],
      conflicts: [],
      mergeWarnings: [],
    };

    world.proposals.set(proposalId, record);

    return {
      proposalId,
      state: record.state,
      ingestedRegistryVersion: record.ingestedRegistryVersion,
    };
  }

  promoteProposal(worldId, proposalId, options = {}) {
    const world = this._requireWorld(worldId);
    const record = world.proposals.get(proposalId);

    if (!record) {
      throw new Error(`Proposal "${proposalId}" does not exist in world "${worldId}".`);
    }

    if (record.state === 'accepted') {
      return {
        proposalId,
        state: 'accepted',
        registrySnapshotId: record.registrySnapshotId,
        registryVersion: world.registryVersion,
        validationErrors: [],
        conflicts: [],
        warnings: record.mergeWarnings.slice(),
      };
    }

    if (Number.isInteger(options.expectedRegistryVersion)
      && options.expectedRegistryVersion !== world.registryVersion) {
      record.state = 'contested';
      record.validationErrors = [
        `registry version advanced from ${options.expectedRegistryVersion} to ${world.registryVersion}`,
      ];
      record.updatedAt = nowIso(this._now);
      return {
        proposalId,
        state: record.state,
        registrySnapshotId: null,
        registryVersion: world.registryVersion,
        validationErrors: record.validationErrors.slice(),
        conflicts: [],
        warnings: [],
      };
    }

    const validation = validateFormalProposal(record.proposal);
    if (!validation.valid) {
      record.state = 'contested';
      record.validationErrors = validation.errors.slice();
      record.updatedAt = nowIso(this._now);
      return {
        proposalId,
        state: record.state,
        registrySnapshotId: null,
        registryVersion: world.registryVersion,
        validationErrors: validation.errors.slice(),
        conflicts: [],
        warnings: [],
      };
    }

    const nextRegistry = world.symbolRegistry.clone();
    const mergeResult = nextRegistry.mergeDeclarations(record.proposal.declarations, {
      declaredIn: `proposal:${proposalId}`,
    });

    if (mergeResult.conflicts.length > 0) {
      record.state = 'contested';
      record.conflicts = deepClone(mergeResult.conflicts);
      record.mergeWarnings = deepClone(mergeResult.warnings || []);
      record.validationErrors = [];
      record.updatedAt = nowIso(this._now);
      return {
        proposalId,
        state: record.state,
        registrySnapshotId: null,
        registryVersion: world.registryVersion,
        validationErrors: [],
        conflicts: deepClone(mergeResult.conflicts),
        warnings: deepClone(mergeResult.warnings || []),
      };
    }

    const check = runSolverSanity(options.solverSanityCheck, record.proposal, worldId);
    if (!check.ok) {
      record.state = 'contested';
      record.validationErrors = [check.reason || 'solver sanity check failed'];
      record.updatedAt = nowIso(this._now);
      return {
        proposalId,
        state: record.state,
        registrySnapshotId: null,
        registryVersion: world.registryVersion,
        validationErrors: record.validationErrors.slice(),
        conflicts: [],
        warnings: deepClone(mergeResult.warnings || []),
      };
    }

    world.symbolRegistry = nextRegistry;
    world.registryVersion += 1;
    const registrySnapshot = world.symbolRegistry.createSnapshot();

    record.state = 'accepted';
    record.registrySnapshotId = registrySnapshot.snapshotId;
    record.validationErrors = [];
    record.conflicts = [];
    record.mergeWarnings = deepClone(mergeResult.warnings || []);
    record.updatedAt = nowIso(this._now);

    appendProposalFragments(world, record);
    incrementProposalSymbolUsage(world, record.proposal);

    return {
      proposalId,
      state: record.state,
      registrySnapshotId: record.registrySnapshotId,
      registryVersion: world.registryVersion,
      validationErrors: [],
      conflicts: [],
      warnings: deepClone(mergeResult.warnings || []),
    };
  }

  getProposal(worldId, proposalId) {
    const world = this._requireWorld(worldId);
    const record = world.proposals.get(proposalId);
    return record ? deepClone(record) : null;
  }

  listProposals(worldId) {
    const world = this._requireWorld(worldId);
    return [...world.proposals.values()]
      .map((record) => deepClone(record))
      .sort((left, right) => left.proposalId.localeCompare(right.proposalId));
  }

  listFragments(worldId, options = {}) {
    const world = this._requireWorld(worldId);
    const includeRestricted = options.includeRestricted !== false;

    return [...world.fragments.values()]
      .filter((fragment) => includeRestricted || !fragment.restrictedProvenance)
      .map((fragment) => deepClone(fragment))
      .sort((left, right) => left.fragmentId.localeCompare(right.fragmentId));
  }

  createSnapshot(worldId, options = {}) {
    const world = this._requireWorld(worldId);
    world.counters.snapshot += 1;

    const snapshotId = `snap_${String(world.counters.snapshot).padStart(4, '0')}`;
    const snapshot = {
      snapshotId,
      worldId,
      label: options.label || null,
      createdAt: nowIso(this._now),
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

  getSnapshot(worldId, snapshotId) {
    const world = this._requireWorld(worldId);
    const snapshot = world.snapshots.get(snapshotId);
    return snapshot ? deepClone(snapshot) : null;
  }

  forkWorld({ fromWorldId, fromSnapshotId, newWorldId }) {
    const sourceWorld = this._requireWorld(fromWorldId);
    const snapshot = sourceWorld.snapshots.get(fromSnapshotId);

    if (!snapshot) {
      throw new Error(`Snapshot "${fromSnapshotId}" does not exist in world "${fromWorldId}".`);
    }

    return this.createWorld(newWorldId, {
      fromSnapshot: snapshot,
      parentWorldId: fromWorldId,
      parentSnapshotId: fromSnapshotId,
      sensitivity: snapshot.securityPolicy?.sensitivity || 'internal',
      tracePolicy: snapshot.securityPolicy || undefined,
    });
  }

  compareWorlds(leftWorldId, rightWorldId, options = {}) {
    const leftWorld = this._requireWorld(leftWorldId);
    const rightWorld = this._requireWorld(rightWorldId);
    const includeRestricted = options.includeRestricted === true;

    const leftKeys = acceptedAssertionKeys(leftWorld, { includeRestricted });
    const rightKeys = acceptedAssertionKeys(rightWorld, { includeRestricted });

    return {
      leftWorldId,
      rightWorldId,
      includeRestricted,
      onlyInLeft: [...leftKeys].filter((key) => !rightKeys.has(key)).sort(),
      onlyInRight: [...rightKeys].filter((key) => !leftKeys.has(key)).sort(),
    };
  }

  buildDeterministicReplayBundle(worldId, snapshotId = null) {
    const world = this._requireWorld(worldId);
    const source = snapshotId ? world.snapshots.get(snapshotId) : null;

    if (snapshotId && !source) {
      throw new Error(`Snapshot "${snapshotId}" does not exist in world "${worldId}".`);
    }

    const replaySource = source || {
      worldId,
      snapshotId: 'live',
      registryVersion: world.registryVersion,
      strategy: world.strategy,
      proposals: [...world.proposals.values()],
      fragments: [...world.fragments.values()],
    };

    const acceptedProposals = replaySource.proposals
      .filter((proposal) => proposal.state === 'accepted')
      .map((proposal) => ({
        proposalId: proposal.proposalId,
        proposal: deepClone(proposal.proposal),
        registrySnapshotId: proposal.registrySnapshotId,
      }));

    return {
      worldId,
      snapshotId: snapshotId || 'live',
      replayMode: 'ir-and-solver-only',
      registryVersion: replaySource.registryVersion,
      strategy: deepClone(replaySource.strategy),
      acceptedProposals,
      fragments: replaySource.fragments.map((fragment) => deepClone(fragment)),
    };
  }

  executeWorldActions(actions, options = {}) {
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
          const result = this.createWorld(params.worldId, {
            sensitivity: params.sensitivity,
          });
          currentWorldId = result.worldId;
          capture(action.captureAs, result.worldId, captures);
          break;
        }
        case 'setStrategy': {
          const worldId = resolveRef(params.worldId || currentWorldId, captures);
          this.setStrategy(worldId, params);
          currentWorldId = worldId;
          break;
        }
        case 'setWorldPolicy': {
          const worldId = resolveRef(params.worldId || currentWorldId, captures);
          this.setWorldPolicy(worldId, params);
          currentWorldId = worldId;
          break;
        }
        case 'ingestProposal': {
          const worldId = resolveRef(params.worldId || currentWorldId, captures);
          if (!params.formalProposal) {
            throw new Error('ingestProposal.params.formalProposal is required in SDK action execution.');
          }
          const result = this.ingestProposal(worldId, params.formalProposal);
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
          this.promoteProposal(worldId, proposalId, { expectedRegistryVersion });
          currentWorldId = worldId;
          break;
        }
        case 'snapshot': {
          const worldId = resolveRef(params.worldId || currentWorldId, captures);
          const result = this.createSnapshot(worldId, { label: params.label || null });
          capture(action.captureAs, result.snapshotId, captures);
          currentWorldId = worldId;
          break;
        }
        case 'forkWorld': {
          const fromWorldId = resolveRef(params.fromWorldId, captures);
          const fromSnapshotId = resolveRef(params.fromSnapshotId, captures);
          const result = this.forkWorld({
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
          this._requireWorld(currentWorldId);
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

  _requireWorld(worldId) {
    const world = this._worlds.get(worldId);
    if (!world) {
      throw new Error(`World "${worldId}" does not exist.`);
    }
    return world;
  }
}

function createEmptyWorld({ worldId, now, parentWorldId, parentSnapshotId, sensitivity, tracePolicy }) {
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

function hydrateWorldFromSnapshot(world, snapshot) {
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

function appendProposalFragments(world, proposalRecord) {
  const existingKeys = new Set(
    [...world.fragments.values()].map((fragment) => `${fragment.proposalId}:${fragment.assertionId}`),
  );

  for (const assertion of proposalRecord.proposal.assertions || []) {
    const key = `${proposalRecord.proposalId}:${assertion.assertionId}`;
    if (existingKeys.has(key)) {
      continue;
    }

    world.counters.fragment += 1;
    const fragmentId = `frag_${String(world.counters.fragment).padStart(5, '0')}`;

    world.fragments.set(fragmentId, {
      fragmentId,
      proposalId: proposalRecord.proposalId,
      assertionId: assertion.assertionId,
      role: assertion.role,
      expr: deepClone(assertion.expr),
      status: proposalRecord.state,
      source: deepClone(proposalRecord.proposal.source),
      tags: deepClone(proposalRecord.proposal.tags || []),
      restrictedProvenance: assertion.restrictedProvenance === true
        || proposalRecord.proposal.source?.restrictedProvenance === true,
    });
  }
}

function incrementProposalSymbolUsage(world, proposal) {
  const symbols = new Set();

  for (const declaration of proposal.declarations || []) {
    if (typeof declaration.name === 'string' && declaration.name) {
      symbols.add(declaration.name);
    }
  }

  for (const assertion of proposal.assertions || []) {
    for (const symbol of collectReferencedSymbols(assertion.expr)) {
      symbols.add(symbol);
    }
  }

  for (const symbol of collectReferencedSymbols(proposal.queryPlan?.goal)) {
    symbols.add(symbol);
  }

  for (const symbol of symbols) {
    world.symbolRegistry.incrementUsage(symbol, 1);
  }
}

function runSolverSanity(check, proposal, worldId) {
  if (typeof check !== 'function') {
    return { ok: true };
  }

  const result = check({ proposal, worldId });
  if (result === true) {
    return { ok: true };
  }

  if (result === false) {
    return { ok: false, reason: 'solver sanity check returned false' };
  }

  if (result && typeof result === 'object') {
    return {
      ok: result.ok !== false,
      reason: result.reason || null,
    };
  }

  return { ok: true };
}

function acceptedAssertionKeys(world, options = {}) {
  const includeRestricted = options.includeRestricted === true;
  const keys = new Set();
  for (const fragment of world.fragments.values()) {
    if (fragment.status !== 'accepted') {
      continue;
    }
    if (!includeRestricted && fragment.restrictedProvenance) {
      continue;
    }
    keys.add(`${fragment.proposalId}:${fragment.assertionId}`);
  }
  return keys;
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
