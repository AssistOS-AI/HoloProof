import test from 'node:test';
import assert from 'node:assert/strict';
import {
  ChatOrchestrator,
  SolverSessionAdapter,
  WorldManager,
} from '../src/index.mjs';
import { makeValidProposal } from './fixtures.mjs';

function fakeLlmClient() {
  return {
    async complete(input = {}) {
      const prompt = String(input.userPrompt || '');

      if (prompt.includes('Question:')) {
        return {
          text: JSON.stringify({
            declarations: [],
            assertions: [],
            queryPlan: {
              verificationMode: 'entailment',
              goal: {
                op: 'call',
                symbol: 'eligible',
                args: [{ op: 'const', name: 'Ana' }],
              },
            },
            ambiguities: [],
            tags: ['query'],
          }),
        };
      }

      return {
        text: JSON.stringify({
          declarations: [
            { kind: 'sort', name: 'Person' },
            { kind: 'const', name: 'Ana', resultSort: 'Person' },
            { kind: 'predicate', name: 'eligible', argSorts: ['Person'], resultSort: 'Bool' },
          ],
          assertions: [
            {
              assertionId: 'ax_ing_1',
              role: 'fact',
              expr: { op: 'call', symbol: 'eligible', args: [{ op: 'const', name: 'Ana' }] },
            },
          ],
          queryPlan: {
            verificationMode: 'consistency',
            goal: null,
          },
          ambiguities: [],
          tags: ['ingest'],
        }),
      };
    },
  };
}

function fakeSolverAdapter() {
  return new SolverSessionAdapter({
    transportFactory: () => ({
      async sendAndReceive(command) {
        if (command === '(check-sat)') {
          return 'unsat';
        }
        if (command === '(get-unsat-core)') {
          return '(hp_query_negated_goal)';
        }
        if (command === '(get-model)') {
          return '(model)';
        }
        return '';
      },
      close() {},
      onCrash() {
        return () => {};
      },
    }),
  });
}

test('ChatOrchestrator handles ingest and query turns using SDK flow', async () => {
  const worldManager = new WorldManager();
  worldManager.createWorld('world_main');

  const baseProposal = makeValidProposal({ proposalId: 'fp_seed' });
  worldManager.ingestProposal('world_main', baseProposal);
  worldManager.promoteProposal('world_main', 'fp_seed');

  const orchestrator = new ChatOrchestrator({
    worldManager,
    solverAdapter: fakeSolverAdapter(),
    llmClient: fakeLlmClient(),
    defaultWorldId: 'world_main',
  });

  const ingest = await orchestrator.processTurn({
    kind: 'ingest',
    worldId: 'world_main',
    text: 'Ana is eligible.',
    sourceId: 'doc_ingest',
  });
  assert.equal(ingest.kind, 'ingest');
  assert.equal(typeof ingest.ok, 'boolean');

  const query = await orchestrator.processTurn({
    kind: 'query',
    worldId: 'world_main',
    text: 'Is Ana eligible?',
  });

  assert.equal(query.kind, 'query');
  assert.equal(query.ok, true);
  assert.ok(query.response.message.length > 0);
  assert.ok(['answer', 'ask-user', 'llm-autofill'].includes(query.response.action));
});

test('ChatOrchestrator supports world action routing', async () => {
  const orchestrator = new ChatOrchestrator({
    worldManager: new WorldManager(),
    solverAdapter: fakeSolverAdapter(),
    llmClient: fakeLlmClient(),
  });

  const created = await orchestrator.processTurn({
    kind: 'world-action',
    action: { type: 'create-world', worldId: 'w1' },
  });
  assert.equal(created.type, 'create-world');

  const switched = await orchestrator.processTurn({
    kind: 'world-action',
    action: { type: 'switch-world', worldId: 'w1' },
  });
  assert.equal(switched.world.worldId, 'w1');
});
