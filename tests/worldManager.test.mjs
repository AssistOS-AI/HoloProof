import test from 'node:test';
import assert from 'node:assert/strict';
import { WorldManager } from '../src/sdk/worldManager.mjs';
import { makeValidProposal } from './fixtures.mjs';

test('WorldManager ingests and promotes valid proposals', () => {
  const manager = new WorldManager({ now: () => Date.parse('2026-02-11T12:00:00.000Z') });
  manager.createWorld('world_main');

  const proposal = makeValidProposal();
  manager.ingestProposal('world_main', proposal);

  const promoted = manager.promoteProposal('world_main', proposal.proposalId);

  assert.equal(promoted.state, 'accepted');
  assert.ok(promoted.registrySnapshotId.startsWith('reg_'));
  assert.equal(promoted.registryVersion, 1);

  const fragments = manager.listFragments('world_main');
  assert.equal(fragments.length, 2);
  assert.ok(fragments.every((fragment) => fragment.status === 'accepted'));
});

test('WorldManager marks conflicting symbol declarations as contested', () => {
  const manager = new WorldManager();
  manager.createWorld('world_main');

  const first = makeValidProposal({ proposalId: 'fp_a' });
  manager.ingestProposal('world_main', first);
  manager.promoteProposal('world_main', 'fp_a');

  const conflicting = makeValidProposal({
    proposalId: 'fp_b',
    declarations: [
      { kind: 'sort', name: 'Person' },
      { kind: 'predicate', name: 'eligible', argSorts: ['Person', 'Person'], resultSort: 'Bool' },
    ],
  });

  manager.ingestProposal('world_main', conflicting);
  const promoted = manager.promoteProposal('world_main', 'fp_b');

  assert.equal(promoted.state, 'contested');
  assert.equal(promoted.conflicts.length, 1);
});

test('WorldManager supports optional registry version compare-and-swap check', () => {
  const manager = new WorldManager();
  manager.createWorld('world_main');

  const first = makeValidProposal({ proposalId: 'fp_a' });
  const second = makeValidProposal({ proposalId: 'fp_b' });
  manager.ingestProposal('world_main', first);
  manager.ingestProposal('world_main', second);

  manager.promoteProposal('world_main', 'fp_a');
  const failed = manager.promoteProposal('world_main', 'fp_b', { expectedRegistryVersion: 0 });

  assert.equal(failed.state, 'contested');
  assert.ok(failed.validationErrors.some((error) => error.includes('registry version advanced')));
});

test('WorldManager snapshots and forks isolate subsequent changes', () => {
  const manager = new WorldManager();
  manager.createWorld('world_main');

  const first = makeValidProposal({ proposalId: 'fp_base' });
  manager.ingestProposal('world_main', first);
  manager.promoteProposal('world_main', 'fp_base');

  const snapshot = manager.createSnapshot('world_main', { label: 'baseline' });
  manager.forkWorld({
    fromWorldId: 'world_main',
    fromSnapshotId: snapshot.snapshotId,
    newWorldId: 'world_alt',
  });

  const second = makeValidProposal({
    proposalId: 'fp_alt',
    assertions: [
      {
        assertionId: 'ax_alt',
        role: 'fact',
        expr: { op: 'call', symbol: 'eligible', args: [{ op: 'const', name: 'Ana' }] },
      },
    ],
  });

  manager.ingestProposal('world_alt', second);
  manager.promoteProposal('world_alt', 'fp_alt');

  const parentFragments = manager.listFragments('world_main');
  const childFragments = manager.listFragments('world_alt');

  assert.equal(parentFragments.length, 2);
  assert.equal(childFragments.length, 3);

  const diff = manager.compareWorlds('world_main', 'world_alt');
  assert.deepEqual(diff.onlyInLeft, []);
  assert.deepEqual(diff.onlyInRight, ['fp_alt:ax_alt']);
});

test('WorldManager executeWorldActions supports capture references', () => {
  const manager = new WorldManager();
  const proposal = makeValidProposal({ proposalId: 'fp_actions' });

  const result = manager.executeWorldActions([
    { action: 'createWorld', params: { worldId: 'w_actions' } },
    { action: 'ingestProposal', params: { formalProposal: proposal }, captureAs: 'proposalId' },
    { action: 'promoteProposal', params: { proposalId: '$proposalId' } },
    { action: 'snapshot', params: { label: 's1' }, captureAs: 'snap1' },
    {
      action: 'forkWorld',
      params: { fromWorldId: 'w_actions', fromSnapshotId: '$snap1', newWorldId: 'w_actions_alt' },
    },
    { action: 'switchWorld', params: { worldId: 'w_actions_alt' } },
  ]);

  assert.equal(result.currentWorldId, 'w_actions_alt');
  assert.equal(result.captures.proposalId, 'fp_actions');
  assert.ok(typeof result.captures.snap1 === 'string');
});

test('WorldManager creates deterministic replay bundle from accepted IR', () => {
  const manager = new WorldManager();
  manager.createWorld('world_main');

  const proposal = makeValidProposal({ proposalId: 'fp_replay' });
  manager.ingestProposal('world_main', proposal);
  manager.promoteProposal('world_main', proposal.proposalId);

  const snapshot = manager.createSnapshot('world_main', { label: 'ready' });
  const replay = manager.buildDeterministicReplayBundle('world_main', snapshot.snapshotId);

  assert.equal(replay.replayMode, 'ir-and-solver-only');
  assert.equal(replay.acceptedProposals.length, 1);
  assert.equal(replay.acceptedProposals[0].proposalId, 'fp_replay');
});

test('WorldManager supports deleteWorld with child protection', () => {
  const manager = new WorldManager();
  manager.createWorld('world_main');
  const snapshot = manager.createSnapshot('world_main', { label: 's1' });
  manager.forkWorld({
    fromWorldId: 'world_main',
    fromSnapshotId: snapshot.snapshotId,
    newWorldId: 'world_child',
  });

  const blocked = manager.deleteWorld('world_main');
  assert.equal(blocked.deleted, false);
  assert.equal(blocked.reason, 'has-children');

  const deletedChild = manager.deleteWorld('world_child');
  assert.equal(deletedChild.deleted, true);

  const deletedParent = manager.deleteWorld('world_main');
  assert.equal(deletedParent.deleted, true);
});

test('WorldManager exposes registry context and supports export/import', () => {
  const manager = new WorldManager();
  manager.createWorld('world_main');

  const proposal = makeValidProposal({ proposalId: 'fp_export' });
  manager.ingestProposal('world_main', proposal);
  manager.promoteProposal('world_main', 'fp_export');

  const context = manager.getRegistryContext('world_main', {
    strategy: 'usage-topk',
    maxSymbols: 3,
    queryTerms: 'eligible',
  });
  assert.equal(context.strategy, 'usage-topk');
  assert.ok(context.symbols.length > 0);

  const dump = manager.exportWorld('world_main');
  const restored = new WorldManager();
  restored.importWorld(dump);

  const restoredWorld = restored.getWorld('world_main');
  assert.equal(restoredWorld.proposalCount, 1);
  assert.equal(restoredWorld.fragmentCount, 2);
});

test('WorldManager promoteProposalAsync supports async sanity checks', async () => {
  const manager = new WorldManager();
  manager.createWorld('world_main');
  const proposal = makeValidProposal({ proposalId: 'fp_async' });
  manager.ingestProposal('world_main', proposal);

  const promoted = await manager.promoteProposalAsync('world_main', 'fp_async', {
    solverSanityCheck: async () => ({ ok: true }),
  });

  assert.equal(promoted.state, 'accepted');
});
