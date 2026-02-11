import test from 'node:test';
import assert from 'node:assert/strict';
import { collectReferencedSymbols, validateFormalProposal } from '../src/sdk/formalProposal.mjs';
import { makeValidProposal } from './fixtures.mjs';

test('validateFormalProposal accepts a valid proposal', () => {
  const proposal = makeValidProposal();
  const result = validateFormalProposal(proposal);

  assert.equal(result.valid, true);
  assert.deepEqual(result.errors, []);
});

test('validateFormalProposal rejects unsupported expression operators', () => {
  const proposal = makeValidProposal({
    assertions: [
      {
        assertionId: 'ax_1',
        role: 'axiom',
        expr: { op: 'custom-op', args: [] },
      },
    ],
  });

  const result = validateFormalProposal(proposal);

  assert.equal(result.valid, false);
  assert.ok(result.errors.some((line) => line.includes('custom-op')));
});

test('validateFormalProposal rejects invalid schema version', () => {
  const proposal = makeValidProposal({ schemaVersion: 'wrong.schema.v1' });
  const result = validateFormalProposal(proposal);

  assert.equal(result.valid, false);
  assert.ok(result.errors.some((line) => line.includes('schemaVersion')));
});

test('validateFormalProposal requires logic field', () => {
  const proposal = makeValidProposal();
  delete proposal.logic;

  const result = validateFormalProposal(proposal);

  assert.equal(result.valid, false);
  assert.ok(result.errors.some((line) => line.includes('logic')));
});

test('validateFormalProposal rejects reserved SMT command identifiers', () => {
  const proposal = makeValidProposal({
    declarations: [
      { kind: 'sort', name: 'Person' },
      { kind: 'const', name: 'exit', resultSort: 'Person' },
    ],
  });

  const result = validateFormalProposal(proposal);

  assert.equal(result.valid, false);
  assert.ok(result.errors.some((line) => line.includes('declarations[1].name')));
});

test('collectReferencedSymbols extracts predicate and constant names from expressions', () => {
  const proposal = makeValidProposal();
  const expr = proposal.assertions[0].expr;

  const symbols = collectReferencedSymbols(expr);

  assert.deepEqual(symbols.sort(), ['eligible', 'student'].sort());
});
