import test from 'node:test';
import assert from 'node:assert/strict';
import {
  appendSyncProbe,
  buildSyncSentinel,
  decideExpansion,
  extractResponseUntilSentinel,
  parseCheckSatResponse,
  parseSExpressionBlock,
} from '../src/index.mjs';

test('solver stdio protocol appends sync probe and extracts response by sentinel', () => {
  const command = '(check-sat)';
  const sentineled = appendSyncProbe(command, 12);
  const sentinel = buildSyncSentinel(12);

  assert.ok(sentineled.includes(sentinel));

  const buffer = `sat\n${sentinel}\ntrailing`;
  const parsed = extractResponseUntilSentinel(buffer, sentinel);

  assert.equal(parsed.complete, true);
  assert.equal(parsed.responseText, 'sat');
  assert.equal(parsed.remaining, 'trailing');
});

test('solver response parsers handle check-sat and s-expression blocks', () => {
  assert.equal(parseCheckSatResponse('noise\nunknown\n'), 'unknown');
  assert.equal(parseSExpressionBlock('(model (define-fun x () Int 1))'), '(model (define-fun x () Int 1))');
  assert.equal(parseSExpressionBlock('(model (broken)'), null);
});

test('expansion policy stops on max rounds and expands otherwise', () => {
  const expand = decideExpansion({
    round: 1,
    maxRounds: 3,
    currentVerdict: 'unknown',
    remainingCandidates: 20,
    expansionStep: 7,
  });
  assert.equal(expand.action, 'expand');
  assert.equal(expand.nextAddCount, 7);

  const stop = decideExpansion({
    round: 3,
    maxRounds: 3,
    currentVerdict: 'unknown',
    remainingCandidates: 20,
  });
  assert.equal(stop.action, 'stop');
  assert.equal(stop.reason, 'max-rounds-reached');
});
