import { collectReferencedSymbols, validateFormalProposal } from '../formalProposal.mjs';
import { deepClone, ensureRecord, nowIso } from './internalUtils.mjs';

export function ingestProposalRecord(world, proposal, worldId, nowFn) {
  ensureRecord(proposal, 'proposal must be an object.');

  const proposalId = proposal.proposalId;
  if (typeof proposalId !== 'string' || !proposalId.trim()) {
    throw new Error('proposal.proposalId must be a non-empty string.');
  }

  if (world.proposals.has(proposalId)) {
    throw new Error(`Proposal "${proposalId}" already exists in world "${worldId}".`);
  }

  const timestamp = nowIso(nowFn);
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

export function promoteProposalRecord(world, proposalId, worldId, nowFn, options = {}) {
  const context = beginPromotion(world, proposalId, worldId, nowFn, options);
  if (context.earlyResult) {
    return context.earlyResult;
  }

  const sanity = runSolverSanity(options.solverSanityCheck, context.record.proposal, worldId);
  if (!sanity.ok) {
    return rejectBySanity(world, context.record, worldId, nowFn, context.mergeResult, sanity.reason);
  }

  return acceptPromotion(world, context.record, context.nextRegistry, context.mergeResult, nowFn);
}

export async function promoteProposalRecordAsync(world, proposalId, worldId, nowFn, options = {}) {
  const context = beginPromotion(world, proposalId, worldId, nowFn, options);
  if (context.earlyResult) {
    return context.earlyResult;
  }

  const sanity = await runSolverSanityAsync(options.solverSanityCheck, context.record.proposal, worldId);
  if (!sanity.ok) {
    return rejectBySanity(world, context.record, worldId, nowFn, context.mergeResult, sanity.reason);
  }

  return acceptPromotion(world, context.record, context.nextRegistry, context.mergeResult, nowFn);
}

function beginPromotion(world, proposalId, worldId, nowFn, options) {
  const record = world.proposals.get(proposalId);
  if (!record) {
    throw new Error(`Proposal "${proposalId}" does not exist in world "${worldId}".`);
  }

  if (record.state === 'accepted') {
    return {
      record,
      earlyResult: {
        proposalId,
        state: 'accepted',
        registrySnapshotId: record.registrySnapshotId,
        registryVersion: world.registryVersion,
        validationErrors: [],
        conflicts: [],
        warnings: record.mergeWarnings.slice(),
      },
    };
  }

  if (Number.isInteger(options.expectedRegistryVersion)
    && options.expectedRegistryVersion !== world.registryVersion) {
    record.state = 'contested';
    record.validationErrors = [
      `registry version advanced from ${options.expectedRegistryVersion} to ${world.registryVersion}`,
    ];
    record.updatedAt = nowIso(nowFn);
    return {
      record,
      earlyResult: {
        proposalId,
        state: record.state,
        registrySnapshotId: null,
        registryVersion: world.registryVersion,
        validationErrors: record.validationErrors.slice(),
        conflicts: [],
        warnings: [],
      },
    };
  }

  const validation = validateFormalProposal(record.proposal);
  if (!validation.valid) {
    record.state = 'contested';
    record.validationErrors = validation.errors.slice();
    record.updatedAt = nowIso(nowFn);
    return {
      record,
      earlyResult: {
        proposalId,
        state: record.state,
        registrySnapshotId: null,
        registryVersion: world.registryVersion,
        validationErrors: validation.errors.slice(),
        conflicts: [],
        warnings: [],
      },
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
    record.updatedAt = nowIso(nowFn);
    return {
      record,
      earlyResult: {
        proposalId,
        state: record.state,
        registrySnapshotId: null,
        registryVersion: world.registryVersion,
        validationErrors: [],
        conflicts: deepClone(mergeResult.conflicts),
        warnings: deepClone(mergeResult.warnings || []),
      },
    };
  }

  return {
    record,
    nextRegistry,
    mergeResult,
    earlyResult: null,
  };
}

function rejectBySanity(world, record, worldId, nowFn, mergeResult, reason) {
  record.state = 'contested';
  record.validationErrors = [reason || 'solver sanity check failed'];
  record.updatedAt = nowIso(nowFn);
  return {
    proposalId: record.proposalId,
    state: record.state,
    registrySnapshotId: null,
    registryVersion: world.registryVersion,
    validationErrors: record.validationErrors.slice(),
    conflicts: [],
    warnings: deepClone(mergeResult.warnings || []),
  };
}

function acceptPromotion(world, record, nextRegistry, mergeResult, nowFn) {
  world.symbolRegistry = nextRegistry;
  world.registryVersion += 1;
  const registrySnapshot = world.symbolRegistry.createSnapshot();

  record.state = 'accepted';
  record.registrySnapshotId = registrySnapshot.snapshotId;
  record.validationErrors = [];
  record.conflicts = [];
  record.mergeWarnings = deepClone(mergeResult.warnings || []);
  record.updatedAt = nowIso(nowFn);

  appendProposalFragments(world, record);
  incrementProposalSymbolUsage(world, record.proposal);

  return {
    proposalId: record.proposalId,
    state: record.state,
    registrySnapshotId: record.registrySnapshotId,
    registryVersion: world.registryVersion,
    validationErrors: [],
    conflicts: [],
    warnings: deepClone(mergeResult.warnings || []),
  };
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

async function runSolverSanityAsync(check, proposal, worldId) {
  if (typeof check !== 'function') {
    return { ok: true };
  }

  const result = await check({ proposal, worldId });
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
