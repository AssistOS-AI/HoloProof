import test from 'node:test';
import assert from 'node:assert/strict';
import {
  emitDeclarationSmt,
  emitExpressionSmt,
  emitProposalSmtScript,
  emitProposalSmtStatements,
} from '../src/index.mjs';
import { makeValidProposal } from './fixtures.mjs';

test('emitProposalSmtStatements emits deterministic declaration ordering', () => {
  const proposal = makeValidProposal({
    declarations: [
      { kind: 'predicate', name: 'eligible', argSorts: ['Person'], resultSort: 'Bool' },
      { kind: 'sort', name: 'Person' },
      { kind: 'const', name: 'Ana', resultSort: 'Person' },
    ],
  });

  const lines = emitProposalSmtStatements(proposal);

  assert.equal(lines[0], '(set-logic QF_UF)');
  assert.equal(lines[1], '(declare-sort Person 0)');
  assert.equal(lines[2], '(declare-const Ana Person)');
  assert.equal(lines[3], '(declare-fun eligible (Person) Bool)');
});

test('emitExpressionSmt supports ite and distinct operators', () => {
  const expr = {
    op: 'ite',
    args: [
      { op: 'call', symbol: 'eligible', args: [{ op: 'const', name: 'Ana' }] },
      { op: 'distinct', args: [{ op: 'const', name: 'Ana' }, { op: 'const', name: 'Bob' }] },
      { op: 'call', symbol: 'eligible', args: [{ op: 'const', name: 'Bob' }] },
    ],
  };

  const text = emitExpressionSmt(expr);
  assert.ok(text.includes('(ite '));
  assert.ok(text.includes('(distinct Ana Bob)'));
});

test('emitDeclarationSmt rejects reserved internal prefixes', () => {
  assert.throws(() => {
    emitDeclarationSmt({
      kind: 'const',
      name: 'hp_internal_counter',
      resultSort: 'Int',
    });
  }, /reserved prefix/i);
});

test('emitProposalSmtScript can include check-sat and model retrieval commands', () => {
  const proposal = makeValidProposal({ logic: 'QF_UF' });
  const script = emitProposalSmtScript(proposal, {
    includeCheckSat: true,
    includeModel: true,
  });

  assert.ok(script.includes('(set-logic QF_UF)'));
  assert.ok(script.includes('(check-sat)'));
  assert.ok(script.includes('(get-model)'));
});
