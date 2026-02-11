import test from 'node:test';
import assert from 'node:assert/strict';
import { SymbolRegistry } from '../src/sdk/symbolRegistry.mjs';

const BASE_DECLARATIONS = [
  { kind: 'sort', name: 'Person' },
  { kind: 'const', name: 'Ana', resultSort: 'Person' },
  { kind: 'predicate', name: 'eligible', argSorts: ['Person'], resultSort: 'Bool' },
];

test('mergeDeclarations accepts new declarations', () => {
  const registry = new SymbolRegistry();
  const result = registry.mergeDeclarations(BASE_DECLARATIONS, { declaredIn: 'proposal:fp_1' });

  assert.equal(result.conflicts.length, 0);
  assert.equal(result.accepted.length, 3);
  assert.equal(result.warnings.length, 0);
  assert.equal(registry.listEntries().length, 3);
});

test('mergeDeclarations is idempotent for identical signatures', () => {
  const registry = new SymbolRegistry();
  registry.mergeDeclarations(BASE_DECLARATIONS, { declaredIn: 'proposal:fp_1' });

  const result = registry.mergeDeclarations(BASE_DECLARATIONS, { declaredIn: 'proposal:fp_2' });

  assert.equal(result.conflicts.length, 0);
  assert.equal(result.accepted.filter((entry) => entry.type === 'idempotent').length, 3);
});

test('mergeDeclarations reports conflict for incompatible signatures', () => {
  const registry = new SymbolRegistry();
  registry.mergeDeclarations(BASE_DECLARATIONS, { declaredIn: 'proposal:fp_1' });

  const conflictDecl = [
    { kind: 'predicate', name: 'eligible', argSorts: ['Person', 'Person'], resultSort: 'Bool' },
  ];

  const result = registry.mergeDeclarations(conflictDecl, { declaredIn: 'proposal:fp_2' });

  assert.equal(result.conflicts.length, 1);
  assert.equal(result.conflicts[0].symbol, 'eligible');
});

test('toEncodingContext provides symbols and reserved prefixes', () => {
  const registry = new SymbolRegistry();
  registry.mergeDeclarations(BASE_DECLARATIONS, { declaredIn: 'proposal:fp_1' });
  registry.incrementUsage('eligible', 4);
  registry.incrementUsage('Ana', 1);

  const context = registry.toEncodingContext({ maxSymbols: 2, queryTerms: 'eligibility person' });

  assert.ok(Array.isArray(context.symbols));
  assert.equal(context.symbols.length, 2);
  assert.deepEqual(context.reservedPrefixes, ['hp_internal_']);
  assert.ok(Array.isArray(context.rules));
  assert.equal(context.strategy, 'usage-topk');
  assert.equal(context.symbols[0].symbol, 'eligible');
});

test('mergeDeclarations emits semantic duplicate warnings for structurally equivalent declarations with new names', () => {
  const registry = new SymbolRegistry();
  registry.mergeDeclarations([
    { kind: 'sort', name: 'Person' },
    { kind: 'predicate', name: 'eligible', argSorts: ['Person'], resultSort: 'Bool' },
  ], { declaredIn: 'proposal:fp_1' });

  const result = registry.mergeDeclarations([
    { kind: 'predicate', name: 'qualifies', argSorts: ['Person'], resultSort: 'Bool' },
  ], { declaredIn: 'proposal:fp_2' });

  assert.equal(result.conflicts.length, 0);
  assert.ok(result.warnings.some((warning) => warning.type === 'possible-semantic-duplicate'));
});

test('sort aliases are resolved in structural checks and exposed in encoding context', () => {
  const registry = new SymbolRegistry();
  registry.mergeDeclarations([
    { kind: 'sort', name: 'Person', aliases: ['Human'] },
    { kind: 'predicate', name: 'eligible', argSorts: ['Person'], resultSort: 'Bool' },
  ], { declaredIn: 'proposal:fp_1' });

  const context = registry.toEncodingContext();
  assert.ok(context.sortAliases.some((alias) => alias.alias === 'human' && alias.canonicalSort === 'Person'));
  assert.equal(registry.resolveSort('Human'), 'Person');
});

test('toEncodingContext supports vsa-similarity-topk strategy', () => {
  const registry = new SymbolRegistry();
  registry.mergeDeclarations([
    { kind: 'sort', name: 'Person' },
    { kind: 'predicate', name: 'eligible', argSorts: ['Person'], resultSort: 'Bool', semanticHint: 'benefit qualification' },
    { kind: 'predicate', name: 'blocked', argSorts: ['Person'], resultSort: 'Bool', semanticHint: 'security denial and sanctions' },
  ], { declaredIn: 'proposal:fp_1' });

  registry.incrementUsage('blocked', 50);
  registry.incrementUsage('eligible', 1);

  const usageContext = registry.toEncodingContext({
    strategy: 'usage-topk',
    maxSymbols: 1,
    queryTerms: 'benefit qualification',
  });

  const vsaContext = registry.toEncodingContext({
    strategy: 'vsa-similarity-topk',
    maxSymbols: 1,
    queryTerms: 'benefit qualification',
    vectorDim: 256,
  });

  assert.equal(usageContext.strategy, 'usage-topk');
  assert.equal(vsaContext.strategy, 'vsa-similarity-topk');
  assert.equal(usageContext.symbols.length, 1);
  assert.equal(vsaContext.symbols.length, 1);
  assert.equal(vsaContext.symbols[0].symbol, 'eligible');
});
