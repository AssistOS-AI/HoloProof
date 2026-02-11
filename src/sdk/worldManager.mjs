import { executeWorldActions as runWorldActions } from './world/actionsRunner.mjs';
import { acceptedAssertionKeys, deepClone, ensureRecord, normalizeSensitivity } from './world/internalUtils.mjs';
import { ingestProposalRecord, promoteProposalRecord, promoteProposalRecordAsync } from './world/promotion.mjs';
import {
  createEmptyWorld,
  createSnapshotRecord,
  exportSerializedWorld,
  hydrateWorldFromSnapshot,
  importSerializedWorld,
  summarizeWorld,
} from './world/worldState.mjs';

export class WorldManager {
  constructor(options = {}) {
    this._worlds = new Map();
    this._now = typeof options.now === 'function' ? options.now : Date.now;
  }

  listWorldIds() {
    return [...this._worlds.keys()].sort((left, right) => left.localeCompare(right));
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
    return summarizeWorld(this._requireWorld(worldId));
  }

  deleteWorld(worldId, options = {}) {
    const world = this._worlds.get(worldId);
    if (!world) {
      return { deleted: false, reason: 'not-found' };
    }

    const requireNoChildren = options.requireNoChildren !== false;
    if (requireNoChildren) {
      const hasChild = [...this._worlds.values()].some((candidate) => candidate.parentWorldId === worldId);
      if (hasChild) {
        return { deleted: false, reason: 'has-children' };
      }
    }

    this._worlds.delete(worldId);
    return {
      deleted: true,
      worldId,
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

  getStrategy(worldId) {
    const world = this._requireWorld(worldId);
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

  getRegistryEntries(worldId) {
    const world = this._requireWorld(worldId);
    return deepClone(world.symbolRegistry.listEntries());
  }

  getRegistryContext(worldId, options = {}) {
    const world = this._requireWorld(worldId);
    return deepClone(world.symbolRegistry.toEncodingContext(options));
  }

  ingestProposal(worldId, proposal) {
    const world = this._requireWorld(worldId);
    return ingestProposalRecord(world, proposal, worldId, this._now);
  }

  promoteProposal(worldId, proposalId, options = {}) {
    const world = this._requireWorld(worldId);
    return promoteProposalRecord(world, proposalId, worldId, this._now, options);
  }

  async promoteProposalAsync(worldId, proposalId, options = {}) {
    const world = this._requireWorld(worldId);
    return promoteProposalRecordAsync(world, proposalId, worldId, this._now, options);
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
    return createSnapshotRecord(worldId, world, this._now, options);
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

  exportWorld(worldId) {
    const world = this._requireWorld(worldId);
    return exportSerializedWorld(world);
  }

  importWorld(serializedWorld, options = {}) {
    ensureRecord(serializedWorld, 'serializedWorld must be an object.');
    const worldId = serializedWorld.worldId;
    if (typeof worldId !== 'string' || !worldId.trim()) {
      throw new Error('serializedWorld.worldId must be a non-empty string.');
    }

    if (this._worlds.has(worldId) && options.overwrite !== true) {
      throw new Error(`World "${worldId}" already exists.`);
    }

    const imported = importSerializedWorld(serializedWorld, { now: this._now });
    this._worlds.set(imported.worldId, imported.world);
    return this.getWorld(imported.worldId);
  }

  executeWorldActions(actions, options = {}) {
    return runWorldActions(this, actions, options);
  }

  _requireWorld(worldId) {
    const world = this._worlds.get(worldId);
    if (!world) {
      throw new Error(`World "${worldId}" does not exist.`);
    }
    return world;
  }
}
