export function makeValidProposal(overrides = {}) {
  return {
    schemaVersion: 'holoproof.formal-proposal.v1',
    proposalId: 'fp_0001',
    worldId: 'world_main',
    source: {
      sourceId: 'doc_1',
      span: { start: 0, end: 32 },
      createdAt: '2026-02-11T12:00:00.000Z',
    },
    declarations: [
      { kind: 'sort', name: 'Person' },
      { kind: 'const', name: 'Ana', resultSort: 'Person' },
      { kind: 'predicate', name: 'student', argSorts: ['Person'], resultSort: 'Bool' },
      { kind: 'predicate', name: 'eligible', argSorts: ['Person'], resultSort: 'Bool' },
    ],
    assertions: [
      {
        assertionId: 'ax_1',
        role: 'axiom',
        expr: {
          op: 'forall',
          vars: [{ name: 'x', sort: 'Person' }],
          body: {
            op: '=>',
            args: [
              { op: 'call', symbol: 'student', args: [{ op: 'var', name: 'x' }] },
              { op: 'call', symbol: 'eligible', args: [{ op: 'var', name: 'x' }] },
            ],
          },
        },
      },
      {
        assertionId: 'ax_2',
        role: 'fact',
        expr: { op: 'call', symbol: 'student', args: [{ op: 'const', name: 'Ana' }] },
      },
    ],
    queryPlan: {
      verificationMode: 'entailment',
      goal: { op: 'call', symbol: 'eligible', args: [{ op: 'const', name: 'Ana' }] },
    },
    ambiguities: [],
    tags: ['eligibility'],
    ...overrides,
  };
}
