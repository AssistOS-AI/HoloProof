import test from 'node:test';
import assert from 'node:assert/strict';
import os from 'node:os';
import path from 'node:path';
import { promises as fs } from 'node:fs';
import {
  JsonFilePersistenceAdapter,
  WorldManager,
  applyTracePolicyForActor,
  canAccessTrace,
  loadWorldIntoManager,
  persistWorldManagerWorld,
} from '../src/index.mjs';
import { makeValidProposal } from './fixtures.mjs';

test('JsonFilePersistenceAdapter saves and loads world snapshots', async (t) => {
  const tempRoot = await fs.mkdtemp(path.join(os.tmpdir(), 'holoproof-worlds-'));
  const baseDir = path.join(tempRoot, 'worlds');
  t.after(async () => {
    await fs.rm(tempRoot, { recursive: true, force: true });
  });

  const manager = new WorldManager();
  manager.createWorld('world_main');
  const proposal = makeValidProposal({ proposalId: 'fp_persist' });
  manager.ingestProposal('world_main', proposal);
  manager.promoteProposal('world_main', 'fp_persist');

  const adapter = new JsonFilePersistenceAdapter({ baseDir });
  await persistWorldManagerWorld(manager, 'world_main', adapter);

  const loadedIds = await adapter.listWorldIds();
  assert.deepEqual(loadedIds, ['world_main']);

  const restoredManager = new WorldManager();
  await loadWorldIntoManager(restoredManager, 'world_main', adapter);
  const world = restoredManager.getWorld('world_main');
  assert.equal(world.proposalCount, 1);
  assert.equal(world.fragmentCount, 2);
});

test('trace access policy redacts sensitive artifacts for unauthorized actor', () => {
  const trace = {
    createdAt: '2026-02-11T12:00:00.000Z',
    accessPolicy: {
      visibility: 'world-members',
      allowedRoles: ['admin'],
    },
    solverArtifacts: {
      model: { x: 1 },
      unsatCore: ['ax_1'],
    },
  };

  assert.equal(canAccessTrace(trace, { actorId: 'u1', roles: ['viewer'] }), false);
  const secured = applyTracePolicyForActor(trace, {
    sensitivity: 'restricted',
    redactModelValues: false,
    allowUnsatCoreDetails: true,
  }, { actorId: 'u1', roles: ['viewer'] });

  assert.equal(secured.allowed, false);
  assert.equal(secured.trace.solverArtifacts.model.redacted, true);
  assert.equal(secured.trace.solverArtifacts.unsatCore.redacted, true);
});
