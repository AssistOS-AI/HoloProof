import { spawn } from 'node:child_process';
import { EventEmitter } from 'node:events';
import {
  appendSyncProbe,
  buildSyncSentinel,
  extractResponseUntilSentinel,
  parseCheckSatResponse,
  parseSExpressionBlock,
} from './stdioProtocol.mjs';
import { emitAssertionSmt } from './smtEmitter.mjs';

const DEFAULT_TIMEOUT_MS = 4000;

const DEFAULT_SOLVER_PROFILES = {
  z3: {
    command: 'z3',
    args: ['-in', '-smt2'],
  },
  cvc5: {
    command: 'cvc5',
    args: ['--lang', 'smt2', '--incremental'],
  },
};

class SolverAdapterError extends Error {
  constructor(message, options = {}) {
    super(message);
    this.name = 'SolverAdapterError';
    this.code = options.code || 'solver-adapter-error';
    this.cause = options.cause || null;
    this.details = options.details || null;
  }
}

export class SolverTimeoutError extends SolverAdapterError {
  constructor(message, options = {}) {
    super(message, { ...options, code: 'solver-timeout' });
    this.name = 'SolverTimeoutError';
  }
}

export class SolverSessionCrashedError extends SolverAdapterError {
  constructor(message, options = {}) {
    super(message, { ...options, code: 'solver-session-crashed' });
    this.name = 'SolverSessionCrashedError';
  }
}

function isRecord(value) {
  return value !== null && typeof value === 'object' && !Array.isArray(value);
}

function positiveInteger(value, fallback) {
  return Number.isInteger(value) && value > 0 ? value : fallback;
}

function normalizeSolverProfile(config = {}) {
  const solverKey = typeof config.solver === 'string' ? config.solver.trim().toLowerCase() : '';
  const fallback = DEFAULT_SOLVER_PROFILES[solverKey] || {};

  const command = typeof config.command === 'string' && config.command.trim()
    ? config.command.trim()
    : fallback.command;

  if (!command) {
    throw new Error('Solver session config must define command or known solver profile.');
  }

  const args = Array.isArray(config.args)
    ? config.args.map((value) => String(value))
    : [...(fallback.args || [])];

  return {
    solver: solverKey || 'custom',
    command,
    args,
  };
}

function normalizeSessionConfig(config = {}) {
  const profile = normalizeSolverProfile(config);

  const session = {
    ...profile,
    logic: typeof config.logic === 'string' && config.logic.trim() ? config.logic.trim() : null,
    timeoutMs: positiveInteger(config.timeoutMs, DEFAULT_TIMEOUT_MS),
    maxMemoryMB: positiveInteger(config.maxMemoryMB, null),
    timeoutOptionKey: typeof config.timeoutOptionKey === 'string' && config.timeoutOptionKey.trim()
      ? config.timeoutOptionKey.trim()
      : null,
    memoryOptionKey: typeof config.memoryOptionKey === 'string' && config.memoryOptionKey.trim()
      ? config.memoryOptionKey.trim()
      : null,
    setOptions: isRecord(config.setOptions) ? { ...config.setOptions } : {},
  };

  return session;
}

function optionKey(name) {
  const trimmed = String(name || '').trim();
  if (!trimmed) {
    return null;
  }
  if (trimmed.startsWith(':')) {
    return trimmed;
  }
  return `:${trimmed}`;
}

function serializeSmtValue(value) {
  if (typeof value === 'boolean') {
    return value ? 'true' : 'false';
  }
  if (typeof value === 'number' && Number.isFinite(value)) {
    return String(value);
  }

  const raw = String(value ?? '').trim();
  if (!raw) {
    return '""';
  }

  if (/^[A-Za-z0-9_+./:-]+$/.test(raw)) {
    return raw;
  }

  const escaped = raw.replaceAll('\\', '\\\\').replaceAll('"', '\\"');
  return `"${escaped}"`;
}

function buildInitCommands(config) {
  const commands = [];

  if (config.logic) {
    commands.push(`(set-logic ${config.logic})`);
  }

  const entries = Object.entries(config.setOptions || {});
  for (const [key, value] of entries) {
    const normalizedKey = optionKey(key);
    if (!normalizedKey) {
      continue;
    }
    commands.push(`(set-option ${normalizedKey} ${serializeSmtValue(value)})`);
  }

  if (config.timeoutOptionKey && Number.isInteger(config.timeoutMs)) {
    commands.push(`(set-option ${optionKey(config.timeoutOptionKey)} ${config.timeoutMs})`);
  }

  if (config.memoryOptionKey && Number.isInteger(config.maxMemoryMB)) {
    commands.push(`(set-option ${optionKey(config.memoryOptionKey)} ${config.maxMemoryMB})`);
  }

  return commands;
}

function normalizeAssertionInput(assertion, options = {}) {
  if (typeof assertion === 'string') {
    const trimmed = assertion.trim();
    if (!trimmed) {
      throw new Error('Assertion string cannot be empty.');
    }
    if (trimmed.startsWith('(assert ')) {
      return trimmed;
    }
    return `(assert ${trimmed})`;
  }

  if (!assertion || typeof assertion !== 'object') {
    throw new Error('Assertion must be a string or expression object.');
  }

  if (assertion.expr) {
    return emitAssertionSmt(assertion, { named: options.named !== false });
  }

  return emitAssertionSmt({ expr: assertion }, { named: false });
}

function parseUnsatCoreSymbols(responseText) {
  const block = parseSExpressionBlock(responseText);
  if (!block) {
    return null;
  }

  const trimmed = block.trim();
  if (!trimmed.startsWith('(') || !trimmed.endsWith(')')) {
    return null;
  }

  const body = trimmed.slice(1, -1).trim();
  if (!body) {
    return [];
  }

  return body.split(/\s+/).filter(Boolean);
}

export function createStdioTransport(config, options = {}) {
  const spawnFn = typeof options.spawnFn === 'function' ? options.spawnFn : spawn;
  const child = spawnFn(config.command, config.args, {
    stdio: ['pipe', 'pipe', 'pipe'],
  });

  const emitter = new EventEmitter();
  let pending = null;
  let stdoutBuffer = '';
  let stderrBuffer = '';
  let closed = false;
  let crashed = false;

  function settlePending(responseText, err = null) {
    if (!pending) {
      return;
    }
    const current = pending;
    pending = null;
    clearTimeout(current.timer);

    if (err) {
      current.reject(err);
      return;
    }
    current.resolve(responseText);
  }

  function drainPending() {
    if (!pending) {
      return;
    }

    const parsed = extractResponseUntilSentinel(stdoutBuffer, pending.sentinel);
    if (!parsed.complete) {
      return;
    }

    stdoutBuffer = parsed.remaining;
    settlePending(parsed.responseText ?? '');
  }

  function crash(reason, cause = null) {
    if (crashed) {
      return;
    }
    crashed = true;

    const err = new SolverSessionCrashedError(`Solver transport crashed: ${reason}`, {
      code: reason,
      cause,
      details: {
        stderr: stderrBuffer.trim() || null,
      },
    });

    settlePending('', err);
    emitter.emit('crash', {
      reason,
      error: err,
    });
  }

  child.stdout.on('data', (chunk) => {
    stdoutBuffer += String(chunk);
    drainPending();
  });

  child.stderr.on('data', (chunk) => {
    stderrBuffer += String(chunk);
    if (stderrBuffer.length > 16000) {
      stderrBuffer = stderrBuffer.slice(-16000);
    }
  });

  child.on('error', (error) => {
    crash('spawn-error', error);
  });

  child.on('exit', (code, signal) => {
    if (closed) {
      return;
    }
    const suffix = signal ? `signal=${signal}` : `code=${code}`;
    crash(`process-exit:${suffix}`);
  });

  async function sendAndReceive(commandText, sequenceId, timeoutMs) {
    if (closed) {
      throw new SolverSessionCrashedError('Cannot send command to closed solver transport.', {
        code: 'transport-closed',
      });
    }

    if (crashed) {
      throw new SolverSessionCrashedError('Cannot send command to crashed solver transport.', {
        code: 'transport-crashed',
      });
    }

    if (pending) {
      throw new SolverAdapterError('Solver command overlap detected in transport.', {
        code: 'command-overlap',
      });
    }

    const sequence = positiveInteger(sequenceId, 1);
    const timeout = positiveInteger(timeoutMs, DEFAULT_TIMEOUT_MS);
    const sentinel = buildSyncSentinel(sequence);
    const payload = appendSyncProbe(commandText, sequence);

    const responsePromise = new Promise((resolve, reject) => {
      const timer = setTimeout(() => {
        settlePending('', new SolverTimeoutError(`Solver command timed out after ${timeout}ms`, {
          details: { timeoutMs: timeout, sentinel },
        }));
      }, timeout);

      pending = {
        sentinel,
        resolve,
        reject,
        timer,
      };
    });

    await new Promise((resolve, reject) => {
      child.stdin.write(payload, (error) => {
        if (error) {
          reject(new SolverSessionCrashedError('Failed writing command to solver stdin.', {
            code: 'stdin-write-failed',
            cause: error,
          }));
          return;
        }
        resolve();
      });
    });

    drainPending();
    return responsePromise;
  }

  function close() {
    if (closed) {
      return;
    }
    closed = true;
    settlePending('', new SolverSessionCrashedError('Solver transport closed while waiting for response.', {
      code: 'transport-closed',
    }));

    try {
      child.stdin.end();
    } catch {
      // Ignore cleanup errors.
    }
    try {
      child.kill('SIGTERM');
    } catch {
      // Ignore cleanup errors.
    }
  }

  return {
    sendAndReceive,
    close,
    onCrash(listener) {
      if (typeof listener !== 'function') {
        return () => {};
      }
      emitter.on('crash', listener);
      return () => emitter.off('crash', listener);
    },
    debugState() {
      return {
        crashed,
        closed,
        stderr: stderrBuffer.trim(),
      };
    },
  };
}

export class SolverSessionAdapter {
  constructor(options = {}) {
    this._sessions = new Map();
    this._counter = 0;
    this._onSessionEvent = typeof options.onSessionEvent === 'function' ? options.onSessionEvent : null;
    this._transportFactory = typeof options.transportFactory === 'function'
      ? options.transportFactory
      : (config) => createStdioTransport(config, { spawnFn: options.spawnFn });
  }

  async openSession(config = {}) {
    const normalized = normalizeSessionConfig(config);
    this._counter += 1;
    const sessionId = `session_${String(this._counter).padStart(4, '0')}`;

    const session = {
      sessionId,
      config: normalized,
      queue: Promise.resolve(),
      sequence: 1,
      transport: null,
      unstable: false,
      closed: false,
      stackDepth: 0,
      lastVerdict: null,
      stableCommands: [],
      initCommands: buildInitCommands(normalized),
      recoveredSinceLastCheck: false,
      unsubCrash: null,
    };

    this._sessions.set(sessionId, session);

    try {
      await this._serialize(session, async () => {
        await this._startTransport(session);
        for (const command of session.initCommands) {
          await this._send(session, command, {
            timeoutMs: session.config.timeoutMs,
            trackStable: true,
          });
        }
      });
    } catch (error) {
      await this._closeSessionInternal(session);
      this._sessions.delete(sessionId);
      throw error;
    }

    return sessionId;
  }

  async push(sessionId) {
    return this._withSession(sessionId, async (session) => {
      await this._send(session, '(push 1)');
      session.stackDepth += 1;
      return session.stackDepth;
    });
  }

  async pop(sessionId, levels = 1) {
    return this._withSession(sessionId, async (session) => {
      const normalizedLevels = positiveInteger(levels, 1);
      await this._send(session, `(pop ${normalizedLevels})`);
      session.stackDepth = Math.max(0, session.stackDepth - normalizedLevels);
      return session.stackDepth;
    });
  }

  async assert(sessionId, assertions, options = {}) {
    return this._withSession(sessionId, async (session) => {
      const items = Array.isArray(assertions) ? assertions : [assertions];
      const commands = items.map((item) => normalizeAssertionInput(item, options));
      const trackStable = options.scope !== 'transient';

      for (const command of commands) {
        await this._send(session, command, { trackStable });
      }

      return {
        count: commands.length,
        stable: trackStable,
      };
    });
  }

  async command(sessionId, commandText, options = {}) {
    return this._withSession(sessionId, async (session) => {
      const command = String(commandText || '').trim();
      if (!command) {
        throw new Error('commandText must be a non-empty SMT command string.');
      }

      const trackStable = options.scope !== 'transient';
      await this._send(session, command, { trackStable });

      return {
        ok: true,
        stable: trackStable,
      };
    });
  }

  async checkSat(sessionId, options = {}) {
    return this._withSession(sessionId, async (session) => {
      const start = Date.now();
      const timeoutMs = positiveInteger(options.timeoutMs, session.config.timeoutMs);
      const assumptions = Array.isArray(options.assumptions) ? options.assumptions : [];
      const recoveredBeforeCheck = session.recoveredSinceLastCheck;
      session.recoveredSinceLastCheck = false;

      if (assumptions.length > 0) {
        await this._send(session, '(push 1)');
        session.stackDepth += 1;
        try {
          for (const assumption of assumptions) {
            await this._send(session, normalizeAssertionInput(assumption, { named: false }), {
              trackStable: false,
            });
          }
        } catch (error) {
          await this._safeTransientPop(session, 1);
          throw error;
        }
      }

      try {
        const response = await this._send(session, '(check-sat)', { timeoutMs });
        const verdict = parseCheckSatResponse(response) || 'unknown';
        session.lastVerdict = verdict;
        const recovered = recoveredBeforeCheck || session.recoveredSinceLastCheck;
        session.recoveredSinceLastCheck = false;

        return {
          verdict,
          elapsedMs: Date.now() - start,
          timeout: false,
          recovered,
          raw: response.trim() || null,
        };
      } catch (error) {
        if (error instanceof SolverTimeoutError) {
          const recovered = recoveredBeforeCheck || session.recoveredSinceLastCheck;
          session.recoveredSinceLastCheck = false;
          return {
            verdict: 'unknown',
            elapsedMs: Date.now() - start,
            timeout: true,
            recovered,
            raw: null,
            error: error.message,
          };
        }
        throw error;
      } finally {
        if (assumptions.length > 0) {
          await this._safeTransientPop(session, 1);
        }
      }
    });
  }

  async getModel(sessionId) {
    return this._withSession(sessionId, async (session) => {
      if (session.lastVerdict !== 'sat') {
        return null;
      }

      const response = await this._send(session, '(get-model)');
      return parseSExpressionBlock(response);
    });
  }

  async getUnsatCore(sessionId) {
    return this._withSession(sessionId, async (session) => {
      if (session.lastVerdict !== 'unsat') {
        return null;
      }

      const response = await this._send(session, '(get-unsat-core)');
      return parseUnsatCoreSymbols(response);
    });
  }

  async reset(sessionId) {
    return this._withSession(sessionId, async (session) => {
      await this._send(session, '(reset)');
      session.stackDepth = 0;
      session.lastVerdict = null;
      session.stableCommands = [];

      for (const command of session.initCommands) {
        await this._send(session, command, { trackStable: true });
      }

      return {
        ok: true,
      };
    });
  }

  async closeSession(sessionId) {
    const session = this._sessions.get(sessionId);
    if (!session) {
      return { closed: false };
    }

    await this._serialize(session, async () => {
      await this._closeSessionInternal(session);
    });

    this._sessions.delete(sessionId);
    return { closed: true };
  }

  getSessionState(sessionId) {
    const session = this._sessions.get(sessionId);
    if (!session) {
      return null;
    }

    return {
      sessionId: session.sessionId,
      stackDepth: session.stackDepth,
      lastVerdict: session.lastVerdict,
      unstable: session.unstable,
      closed: session.closed,
      stableCommandCount: session.stableCommands.length,
      recoveredSinceLastCheck: session.recoveredSinceLastCheck,
    };
  }

  async _withSession(sessionId, operation) {
    const session = this._requireSession(sessionId);
    return this._serialize(session, () => operation(session));
  }

  _serialize(session, operation) {
    const run = session.queue.then(operation);
    session.queue = run.catch(() => {});
    return run;
  }

  _requireSession(sessionId) {
    const session = this._sessions.get(sessionId);
    if (!session) {
      throw new Error(`Unknown solver session "${sessionId}".`);
    }
    if (session.closed) {
      throw new Error(`Solver session "${sessionId}" is closed.`);
    }
    return session;
  }

  async _startTransport(session) {
    const transport = this._transportFactory(session.config);
    if (!transport || typeof transport.sendAndReceive !== 'function') {
      throw new Error('transportFactory must return object with sendAndReceive(command, seq, timeoutMs).');
    }

    session.transport = transport;
    session.unstable = false;

    if (typeof session.unsubCrash === 'function') {
      session.unsubCrash();
    }

    session.unsubCrash = typeof transport.onCrash === 'function'
      ? transport.onCrash((event) => {
        session.unstable = true;
        if (this._onSessionEvent) {
          this._onSessionEvent({
            type: 'session-crashed',
            sessionId: session.sessionId,
            reason: event?.reason || 'unknown',
          });
        }
      })
      : null;
  }

  async _recoverSession(session) {
    const replayCommands = [...session.stableCommands];
    await this._closeTransportOnly(session);
    await this._startTransport(session);

    for (const command of replayCommands) {
      await this._send(session, command, {
        allowRecovery: false,
        trackStable: false,
      });
    }

    session.unstable = false;
    session.recoveredSinceLastCheck = true;
    session.stackDepth = 0;

    if (this._onSessionEvent) {
      this._onSessionEvent({
        type: 'session-recovered',
        sessionId: session.sessionId,
        replayedCommandCount: replayCommands.length,
      });
    }
  }

  async _send(session, command, options = {}) {
    if (session.closed) {
      throw new SolverSessionCrashedError(`Session "${session.sessionId}" is already closed.`, {
        code: 'session-closed',
      });
    }

    if (session.unstable && options.allowRecovery !== false) {
      await this._recoverSession(session);
    }

    if (!session.transport || typeof session.transport.sendAndReceive !== 'function') {
      throw new SolverSessionCrashedError(`Session "${session.sessionId}" has no active transport.`, {
        code: 'missing-transport',
      });
    }

    const timeoutMs = positiveInteger(options.timeoutMs, session.config.timeoutMs);
    const sequenceId = session.sequence;
    session.sequence += 1;

    try {
      const response = await session.transport.sendAndReceive(command, sequenceId, timeoutMs);
      if (options.trackStable) {
        session.stableCommands.push(command);
      }
      return response;
    } catch (error) {
      if (!(error instanceof SolverTimeoutError)) {
        session.unstable = true;
      }
      throw error;
    }
  }

  async _safeTransientPop(session, levels) {
    try {
      await this._send(session, `(pop ${positiveInteger(levels, 1)})`, {
        allowRecovery: false,
      });
      session.stackDepth = Math.max(0, session.stackDepth - positiveInteger(levels, 1));
    } catch {
      session.unstable = true;
      session.stackDepth = 0;
    }
  }

  async _closeTransportOnly(session) {
    if (typeof session.unsubCrash === 'function') {
      session.unsubCrash();
      session.unsubCrash = null;
    }
    if (session.transport && typeof session.transport.close === 'function') {
      session.transport.close();
    }
    session.transport = null;
  }

  async _closeSessionInternal(session) {
    if (session.closed) {
      return;
    }

    session.closed = true;
    await this._closeTransportOnly(session);
  }
}

export function createSolverSessionAdapter(options = {}) {
  return new SolverSessionAdapter(options);
}
