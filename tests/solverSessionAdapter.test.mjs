import test from 'node:test';
import assert from 'node:assert/strict';
import {
  SolverSessionAdapter,
  SolverTimeoutError,
} from '../src/index.mjs';

function createFakeTransport(responder) {
  const crashListeners = new Set();
  const commands = [];
  let closed = false;

  return {
    async sendAndReceive(command, sequenceId, timeoutMs) {
      commands.push({
        command,
        sequenceId,
        timeoutMs,
      });

      if (typeof responder === 'function') {
        return responder({ command, sequenceId, timeoutMs });
      }

      return '';
    },
    onCrash(listener) {
      if (typeof listener !== 'function') {
        return () => {};
      }
      crashListeners.add(listener);
      return () => crashListeners.delete(listener);
    },
    emitCrash(reason = 'test-crash') {
      for (const listener of crashListeners) {
        listener({ reason });
      }
    },
    close() {
      closed = true;
    },
    getCommands() {
      return commands.slice();
    },
    isClosed() {
      return closed;
    },
  };
}

test('SolverSessionAdapter supports lifecycle operations and model retrieval', async () => {
  const transport = createFakeTransport(({ command }) => {
    if (command === '(check-sat)') {
      return 'sat';
    }
    if (command === '(get-model)') {
      return '(model (define-fun x () Int 1))';
    }
    return '';
  });

  const adapter = new SolverSessionAdapter({
    transportFactory: () => transport,
  });

  const sessionId = await adapter.openSession({
    command: 'fake',
    args: [],
    logic: 'QF_UF',
    setOptions: {
      'produce-models': true,
      'produce-unsat-cores': true,
    },
  });

  await adapter.push(sessionId);
  await adapter.assert(sessionId, '(= x x)', { scope: 'transient' });
  const check = await adapter.checkSat(sessionId);
  const model = await adapter.getModel(sessionId);
  await adapter.pop(sessionId, 1);

  assert.equal(check.verdict, 'sat');
  assert.equal(check.timeout, false);
  assert.ok(model.includes('(model'));

  const state = adapter.getSessionState(sessionId);
  assert.equal(state.stackDepth, 0);
  assert.equal(state.lastVerdict, 'sat');

  await adapter.closeSession(sessionId);
  assert.equal(transport.isClosed(), true);
});

test('SolverSessionAdapter recovers session after crash and replays stable commands', async () => {
  const events = [];
  const transports = [];

  const adapter = new SolverSessionAdapter({
    onSessionEvent: (event) => events.push(event),
    transportFactory: () => {
      const transport = createFakeTransport(({ command }) => {
        if (command === '(check-sat)') {
          return 'unsat';
        }
        if (command === '(get-unsat-core)') {
          return '(ax_1 ax_2)';
        }
        return '';
      });
      transports.push(transport);
      return transport;
    },
  });

  const sessionId = await adapter.openSession({
    command: 'fake',
    args: [],
    logic: 'QF_UF',
  });

  await adapter.assert(sessionId, '(assert (! (= x x) :named ax_1))');
  transports[0].emitCrash('simulated');

  const check = await adapter.checkSat(sessionId);
  const core = await adapter.getUnsatCore(sessionId);

  assert.equal(check.verdict, 'unsat');
  assert.equal(check.recovered, true);
  assert.deepEqual(core, ['ax_1', 'ax_2']);
  assert.ok(events.some((event) => event.type === 'session-recovered'));
  assert.equal(transports.length, 2);

  const replayed = transports[1].getCommands().map((item) => item.command);
  assert.ok(replayed.includes('(set-logic QF_UF)'));
  assert.ok(replayed.includes('(assert (! (= x x) :named ax_1))'));
});

test('SolverSessionAdapter maps check-sat timeout to unknown verdict', async () => {
  const adapter = new SolverSessionAdapter({
    transportFactory: () => createFakeTransport(({ command }) => {
      if (command === '(check-sat)') {
        throw new SolverTimeoutError('timed out');
      }
      return '';
    }),
  });

  const sessionId = await adapter.openSession({
    command: 'fake',
    args: [],
  });

  const check = await adapter.checkSat(sessionId, { timeoutMs: 10 });
  assert.equal(check.verdict, 'unknown');
  assert.equal(check.timeout, true);
});
