/*
 * Curated demo scenarios for HoloProof chat.
 * Each scenario contains:
 *   - knowledge: array of FormalProposal objects (declarations + assertions)
 *   - problems: array of { prompt, proposalOverride, simulatedResult }
 */

const V = 'holoproof.formal-proposal.v1';
const ts = '2026-02-11T12:00:00.000Z';
function src(id, end) { return { sourceId: id, span: { start: 0, end }, createdAt: ts }; }

export const DEMO_SCENARIOS = [
  {
    id: 'family-inheritance',
    title: 'Family Inheritance Entailment',
    category: 'Knowledge Graph',
    description: 'Checks whether Ana can inherit under family rules. Demonstrates entailment chains and basic predicate reasoning.',
    knowledge: [
      {
        schemaVersion: V, proposalId: 'fp_fam_001', worldId: '_',
        source: src('fam_rules', 80),
        declarations: [
          { kind: 'sort', name: 'Person' },
          { kind: 'const', name: 'Maria', resultSort: 'Person' },
          { kind: 'const', name: 'Ana', resultSort: 'Person' },
          { kind: 'predicate', name: 'childOf', argSorts: ['Person', 'Person'], resultSort: 'Bool' },
          { kind: 'predicate', name: 'legalHeir', argSorts: ['Person'], resultSort: 'Bool' },
        ],
        assertions: [
          {
            assertionId: 'ax_heir_rule', role: 'axiom',
            expr: {
              op: 'forall', vars: [{ name: 'x', sort: 'Person' }],
              body: { op: '=>', args: [
                { op: 'call', symbol: 'childOf', args: [{ op: 'var', name: 'x' }, { op: 'const', name: 'Maria' }] },
                { op: 'call', symbol: 'legalHeir', args: [{ op: 'var', name: 'x' }] },
              ]},
            },
          },
          {
            assertionId: 'fact_child', role: 'fact',
            expr: { op: 'call', symbol: 'childOf', args: [{ op: 'const', name: 'Ana' }, { op: 'const', name: 'Maria' }] },
          },
        ],
        queryPlan: { verificationMode: 'entailment', goal: { op: 'call', symbol: 'legalHeir', args: [{ op: 'const', name: 'Ana' }] } },
        ambiguities: [],
        tags: ['family', 'inheritance'],
      },
    ],
    problems: [
      {
        prompt: 'Is Ana a legal heir?',
        formalTarget: 'Entailment over predicates childOf and legalHeir.',
        simulatedResult: {
          verdict: 'unsat',
          interpretation: 'entailed',
          reasoning: 'Axiom: childOf(x, Maria) → legalHeir(x).\nFact: childOf(Ana, Maria).\nRefutation of ¬legalHeir(Ana) is unsatisfiable → legalHeir(Ana) is entailed.',
          answer: 'Yes, Ana is a legal heir. The solver confirmed entailment via refutation: the negation of legalHeir(Ana) is unsatisfiable given the axioms.',
          evidence: { fragmentIds: ['frag_00001', 'frag_00002'], unsatCoreIds: ['ax_heir_rule', 'fact_child'], verdict: 'unsat' },
        },
      },
      {
        prompt: 'Is there someone who is NOT a legal heir?',
        formalTarget: 'Model finding: exists x such that ¬legalHeir(x).',
        simulatedResult: {
          verdict: 'sat',
          interpretation: 'satisfiable',
          reasoning: 'Model search for ∃x. ¬legalHeir(x).\nSolver found a witness: a Person distinct from Ana who has no childOf relation to Maria.',
          answer: 'Yes, the solver found a model where a person is not a legal heir — anyone who is not a child of Maria.',
          evidence: { fragmentIds: ['frag_00001'], modelKeys: ['witness_person'], verdict: 'sat' },
        },
      },
    ],
  },

  {
    id: 'access-control',
    title: 'Role Permission Check',
    category: 'Access Control',
    description: 'Checks if a user can access resources based on role hierarchy. Demonstrates permission entailment and unsat core explanation.',
    knowledge: [
      {
        schemaVersion: V, proposalId: 'fp_acl_001', worldId: '_',
        source: src('acl_policy', 120),
        declarations: [
          { kind: 'sort', name: 'User' },
          { kind: 'sort', name: 'Role' },
          { kind: 'const', name: 'Dan', resultSort: 'User' },
          { kind: 'const', name: 'Analyst', resultSort: 'Role' },
          { kind: 'const', name: 'Auditor', resultSort: 'Role' },
          { kind: 'const', name: 'FinanceAdmin', resultSort: 'Role' },
          { kind: 'predicate', name: 'hasRole', argSorts: ['User', 'Role'], resultSort: 'Bool' },
          { kind: 'predicate', name: 'canExportPayroll', argSorts: ['User'], resultSort: 'Bool' },
        ],
        assertions: [
          {
            assertionId: 'ax_export_rule', role: 'axiom',
            expr: {
              op: 'forall', vars: [{ name: 'u', sort: 'User' }],
              body: { op: '=>', args: [
                { op: 'call', symbol: 'canExportPayroll', args: [{ op: 'var', name: 'u' }] },
                { op: 'call', symbol: 'hasRole', args: [{ op: 'var', name: 'u' }, { op: 'const', name: 'FinanceAdmin' }] },
              ]},
            },
          },
          {
            assertionId: 'fact_dan_analyst', role: 'fact',
            expr: { op: 'call', symbol: 'hasRole', args: [{ op: 'const', name: 'Dan' }, { op: 'const', name: 'Analyst' }] },
          },
          {
            assertionId: 'fact_dan_auditor', role: 'fact',
            expr: { op: 'call', symbol: 'hasRole', args: [{ op: 'const', name: 'Dan' }, { op: 'const', name: 'Auditor' }] },
          },
        ],
        queryPlan: { verificationMode: 'entailment', goal: { op: 'call', symbol: 'canExportPayroll', args: [{ op: 'const', name: 'Dan' }] } },
        ambiguities: [],
        tags: ['access-control', 'permissions'],
      },
    ],
    problems: [
      {
        prompt: 'Can Dan export payroll data?',
        formalTarget: 'Permission entailment with role constraints.',
        simulatedResult: {
          verdict: 'sat',
          interpretation: 'not-entailed',
          reasoning: 'Query: canExportPayroll(Dan)?\nRule requires hasRole(Dan, FinanceAdmin).\nDan has roles: Analyst, Auditor — neither is FinanceAdmin.\nRefutation attempt found the negation satisfiable → claim not entailed.',
          answer: 'No, Dan cannot export payroll. He has Analyst and Auditor roles, but the policy requires FinanceAdmin.',
          evidence: { fragmentIds: ['frag_00001', 'frag_00002', 'frag_00003'], modelKeys: ['Dan_roles'], verdict: 'sat' },
        },
      },
    ],
  },

  {
    id: 'scheduling-overlap',
    title: 'Meeting Overlap Detection',
    category: 'Scheduling',
    description: 'Detects overlapping meetings using interval arithmetic. Demonstrates numeric constraint reasoning.',
    knowledge: [
      {
        schemaVersion: V, proposalId: 'fp_sched_001', worldId: '_',
        source: src('calendar', 90),
        declarations: [
          { kind: 'sort', name: 'Meeting' },
          { kind: 'const', name: 'MeetA', resultSort: 'Meeting' },
          { kind: 'const', name: 'MeetB', resultSort: 'Meeting' },
          { kind: 'function', name: 'startTime', argSorts: ['Meeting'], resultSort: 'Int' },
          { kind: 'function', name: 'endTime', argSorts: ['Meeting'], resultSort: 'Int' },
          { kind: 'predicate', name: 'overlaps', argSorts: ['Meeting', 'Meeting'], resultSort: 'Bool' },
        ],
        assertions: [
          {
            assertionId: 'ax_overlap_def', role: 'axiom',
            expr: {
              op: 'forall', vars: [{ name: 'a', sort: 'Meeting' }, { name: 'b', sort: 'Meeting' }],
              body: { op: '=>', args: [
                { op: 'and', args: [
                  { op: '<', args: [{ op: 'call', symbol: 'startTime', args: [{ op: 'var', name: 'a' }] }, { op: 'call', symbol: 'endTime', args: [{ op: 'var', name: 'b' }] }] },
                  { op: '<', args: [{ op: 'call', symbol: 'startTime', args: [{ op: 'var', name: 'b' }] }, { op: 'call', symbol: 'endTime', args: [{ op: 'var', name: 'a' }] }] },
                ]},
                { op: 'call', symbol: 'overlaps', args: [{ op: 'var', name: 'a' }, { op: 'var', name: 'b' }] },
              ]},
            },
          },
          {
            assertionId: 'fact_a_start', role: 'fact',
            expr: { op: '=', args: [{ op: 'call', symbol: 'startTime', args: [{ op: 'const', name: 'MeetA' }] }, { op: 'const', name: 'val_540' }] },
          },
          {
            assertionId: 'fact_a_end', role: 'fact',
            expr: { op: '=', args: [{ op: 'call', symbol: 'endTime', args: [{ op: 'const', name: 'MeetA' }] }, { op: 'const', name: 'val_600' }] },
          },
          {
            assertionId: 'fact_b_start', role: 'fact',
            expr: { op: '=', args: [{ op: 'call', symbol: 'startTime', args: [{ op: 'const', name: 'MeetB' }] }, { op: 'const', name: 'val_570' }] },
          },
          {
            assertionId: 'fact_b_end', role: 'fact',
            expr: { op: '=', args: [{ op: 'call', symbol: 'endTime', args: [{ op: 'const', name: 'MeetB' }] }, { op: 'const', name: 'val_660' }] },
          },
        ],
        queryPlan: { verificationMode: 'entailment', goal: { op: 'call', symbol: 'overlaps', args: [{ op: 'const', name: 'MeetA' }, { op: 'const', name: 'MeetB' }] } },
        ambiguities: [],
        tags: ['scheduling', 'temporal'],
      },
    ],
    problems: [
      {
        prompt: 'Do Meeting A (09:00-10:00) and Meeting B (09:30-11:00) overlap?',
        formalTarget: 'Interval intersection satisfiability.',
        simulatedResult: {
          verdict: 'unsat',
          interpretation: 'entailed',
          reasoning: 'Overlap condition: startA < endB ∧ startB < endA.\n540 < 660 ✓ and 570 < 600 ✓.\nRefutation of ¬overlaps(MeetA, MeetB) is unsatisfiable.',
          answer: 'Yes, the meetings overlap. Meeting A runs until 10:00 and Meeting B starts at 09:30, creating a 30-minute overlap.',
          evidence: { fragmentIds: ['frag_00001', 'frag_00002', 'frag_00003', 'frag_00004', 'frag_00005'], unsatCoreIds: ['ax_overlap_def', 'fact_a_start', 'fact_a_end', 'fact_b_start', 'fact_b_end'], verdict: 'unsat' },
        },
      },
    ],
  },

  {
    id: 'policy-conflict',
    title: 'Contradictory Policy Detection',
    category: 'Consistency',
    description: 'Detects contradictory rules in a policy set. Demonstrates inconsistency detection via unsat core.',
    knowledge: [
      {
        schemaVersion: V, proposalId: 'fp_pol_001', worldId: '_',
        source: src('policy_doc', 100),
        declarations: [
          { kind: 'sort', name: 'Employee' },
          { kind: 'predicate', name: 'isRemote', argSorts: ['Employee'], resultSort: 'Bool' },
          { kind: 'predicate', name: 'isContractor', argSorts: ['Employee'], resultSort: 'Bool' },
          { kind: 'predicate', name: 'mustUseVPN', argSorts: ['Employee'], resultSort: 'Bool' },
        ],
        assertions: [
          {
            assertionId: 'rule1_vpn', role: 'axiom',
            expr: {
              op: 'forall', vars: [{ name: 'e', sort: 'Employee' }],
              body: { op: '=>', args: [
                { op: 'and', args: [
                  { op: 'call', symbol: 'isRemote', args: [{ op: 'var', name: 'e' }] },
                  { op: 'call', symbol: 'isContractor', args: [{ op: 'var', name: 'e' }] },
                ]},
                { op: 'call', symbol: 'mustUseVPN', args: [{ op: 'var', name: 'e' }] },
              ]},
            },
          },
          {
            assertionId: 'rule2_no_vpn', role: 'axiom',
            expr: {
              op: 'forall', vars: [{ name: 'e', sort: 'Employee' }],
              body: { op: '=>', args: [
                { op: 'call', symbol: 'isContractor', args: [{ op: 'var', name: 'e' }] },
                { op: 'not', arg: { op: 'call', symbol: 'mustUseVPN', args: [{ op: 'var', name: 'e' }] } },
              ]},
            },
          },
        ],
        queryPlan: { verificationMode: 'consistency', goal: { op: 'const', name: 'true_val' } },
        ambiguities: [],
        tags: ['policy', 'compliance'],
      },
    ],
    problems: [
      {
        prompt: 'Is this policy set consistent? Rule 1: remote contractors must use VPN. Rule 2: contractors cannot use VPN.',
        formalTarget: 'Global consistency of policy axioms.',
        simulatedResult: {
          verdict: 'unsat',
          interpretation: 'inconsistent',
          reasoning: 'For any remote contractor e:\n  Rule 1: isRemote(e) ∧ isContractor(e) → mustUseVPN(e)\n  Rule 2: isContractor(e) → ¬mustUseVPN(e)\nIf e is both remote and contractor, both rules fire, producing mustUseVPN(e) ∧ ¬mustUseVPN(e).',
          answer: 'The policy set is inconsistent. For any remote contractor, Rule 1 requires VPN and Rule 2 forbids it. These rules conflict.',
          evidence: { unsatCoreIds: ['rule1_vpn', 'rule2_no_vpn'], verdict: 'unsat' },
        },
      },
    ],
  },

  {
    id: 'eligibility-threshold',
    title: 'Scholarship Eligibility Check',
    category: 'Eligibility',
    description: 'Checks eligibility against multiple threshold conditions. Demonstrates conjunctive numeric reasoning.',
    knowledge: [
      {
        schemaVersion: V, proposalId: 'fp_elig_001', worldId: '_',
        source: src('scholarship_rules', 70),
        declarations: [
          { kind: 'sort', name: 'Student' },
          { kind: 'const', name: 'Eva', resultSort: 'Student' },
          { kind: 'function', name: 'gpa', argSorts: ['Student'], resultSort: 'Int' },
          { kind: 'function', name: 'income', argSorts: ['Student'], resultSort: 'Int' },
          { kind: 'predicate', name: 'eligible', argSorts: ['Student'], resultSort: 'Bool' },
        ],
        assertions: [
          {
            assertionId: 'ax_elig_rule', role: 'axiom',
            expr: {
              op: 'forall', vars: [{ name: 's', sort: 'Student' }],
              body: { op: '=>', args: [
                { op: 'and', args: [
                  { op: '>=', args: [{ op: 'call', symbol: 'gpa', args: [{ op: 'var', name: 's' }] }, { op: 'const', name: 'val_35' }] },
                  { op: '<', args: [{ op: 'call', symbol: 'income', args: [{ op: 'var', name: 's' }] }, { op: 'const', name: 'val_40000' }] },
                ]},
                { op: 'call', symbol: 'eligible', args: [{ op: 'var', name: 's' }] },
              ]},
            },
          },
          {
            assertionId: 'fact_gpa', role: 'fact',
            expr: { op: '=', args: [{ op: 'call', symbol: 'gpa', args: [{ op: 'const', name: 'Eva' }] }, { op: 'const', name: 'val_37' }] },
          },
          {
            assertionId: 'fact_income', role: 'fact',
            expr: { op: '=', args: [{ op: 'call', symbol: 'income', args: [{ op: 'const', name: 'Eva' }] }, { op: 'const', name: 'val_42000' }] },
          },
        ],
        queryPlan: { verificationMode: 'entailment', goal: { op: 'call', symbol: 'eligible', args: [{ op: 'const', name: 'Eva' }] } },
        ambiguities: [],
        tags: ['eligibility', 'threshold'],
      },
    ],
    problems: [
      {
        prompt: 'Is Eva eligible for the scholarship? GPA=3.7, income=42k. Rules: GPA>=3.5 and income<40k.',
        formalTarget: 'Conjunctive threshold satisfaction.',
        simulatedResult: {
          verdict: 'sat',
          interpretation: 'not-entailed',
          reasoning: 'GPA condition: 37 >= 35 ✓ (using scaled integers).\nIncome condition: 42000 < 40000 ✗.\nConjunction fails. Rule antecedent not satisfied → eligible(Eva) not entailed.',
          answer: 'No, Eva is not eligible. While her GPA (3.7) meets the minimum (3.5), her income (42k) exceeds the 40k threshold.',
          evidence: { fragmentIds: ['frag_00001', 'frag_00002', 'frag_00003'], modelKeys: ['gpa_Eva', 'income_Eva'], verdict: 'sat' },
        },
      },
    ],
  },

  {
    id: 'graph-reachability',
    title: 'Network Path with Blocked Edge',
    category: 'Graph Reachability',
    description: 'Checks if a target node is reachable when an edge is blocked. Demonstrates reachability with constraints.',
    knowledge: [
      {
        schemaVersion: V, proposalId: 'fp_graph_001', worldId: '_',
        source: src('network_topology', 100),
        declarations: [
          { kind: 'sort', name: 'Node' },
          { kind: 'const', name: 'Internet', resultSort: 'Node' },
          { kind: 'const', name: 'WebServer', resultSort: 'Node' },
          { kind: 'const', name: 'APIGateway', resultSort: 'Node' },
          { kind: 'const', name: 'Database', resultSort: 'Node' },
          { kind: 'predicate', name: 'edge', argSorts: ['Node', 'Node'], resultSort: 'Bool' },
          { kind: 'predicate', name: 'blocked', argSorts: ['Node', 'Node'], resultSort: 'Bool' },
          { kind: 'predicate', name: 'reachable', argSorts: ['Node', 'Node'], resultSort: 'Bool' },
        ],
        assertions: [
          {
            assertionId: 'fact_edge_iw', role: 'fact',
            expr: { op: 'call', symbol: 'edge', args: [{ op: 'const', name: 'Internet' }, { op: 'const', name: 'WebServer' }] },
          },
          {
            assertionId: 'fact_edge_wa', role: 'fact',
            expr: { op: 'call', symbol: 'edge', args: [{ op: 'const', name: 'WebServer' }, { op: 'const', name: 'APIGateway' }] },
          },
          {
            assertionId: 'fact_edge_ad', role: 'fact',
            expr: { op: 'call', symbol: 'edge', args: [{ op: 'const', name: 'APIGateway' }, { op: 'const', name: 'Database' }] },
          },
          {
            assertionId: 'fact_blocked', role: 'fact',
            expr: { op: 'call', symbol: 'blocked', args: [{ op: 'const', name: 'APIGateway' }, { op: 'const', name: 'Database' }] },
          },
          {
            assertionId: 'ax_reach_direct', role: 'axiom',
            expr: {
              op: 'forall', vars: [{ name: 'a', sort: 'Node' }, { name: 'b', sort: 'Node' }],
              body: { op: '=>', args: [
                { op: 'and', args: [
                  { op: 'call', symbol: 'edge', args: [{ op: 'var', name: 'a' }, { op: 'var', name: 'b' }] },
                  { op: 'not', arg: { op: 'call', symbol: 'blocked', args: [{ op: 'var', name: 'a' }, { op: 'var', name: 'b' }] } },
                ]},
                { op: 'call', symbol: 'reachable', args: [{ op: 'var', name: 'a' }, { op: 'var', name: 'b' }] },
              ]},
            },
          },
        ],
        queryPlan: { verificationMode: 'entailment', goal: { op: 'call', symbol: 'reachable', args: [{ op: 'const', name: 'Internet' }, { op: 'const', name: 'Database' }] } },
        ambiguities: [],
        tags: ['network', 'reachability', 'security'],
      },
    ],
    problems: [
      {
        prompt: 'Is the Database reachable from the Internet? Network: Internet→Web→API→DB, firewall blocks API→DB.',
        formalTarget: 'Reachability with blocked edges.',
        simulatedResult: {
          verdict: 'sat',
          interpretation: 'not-entailed',
          reasoning: 'Path Internet→Web→API→DB exists topologically.\nBut edge API→DB is marked blocked by firewall.\nReachability axiom requires edge(a,b) ∧ ¬blocked(a,b).\nSince blocked(API, DB) is true, the API→DB hop does not satisfy the reachability condition.',
          answer: 'No, the Database is not reachable from the Internet. The firewall blocks the API→DB edge, which is the only path to the database.',
          evidence: { fragmentIds: ['frag_00001', 'frag_00002', 'frag_00003', 'frag_00004'], modelKeys: ['blocked_API_DB'], verdict: 'sat' },
        },
      },
    ],
  },

  {
    id: 'contract-clauses',
    title: 'Contradictory Contract Clauses',
    category: 'Contract Analysis',
    description: 'Detects incompatible contract clauses. Demonstrates constraint satisfiability with numeric bounds.',
    knowledge: [
      {
        schemaVersion: V, proposalId: 'fp_contract_001', worldId: '_',
        source: src('contract_doc', 60),
        declarations: [
          { kind: 'function', name: 'deliveryDay', argSorts: [], resultSort: 'Int' },
        ],
        assertions: [
          {
            assertionId: 'clause_a', role: 'axiom',
            expr: { op: '<=', args: [{ op: 'call', symbol: 'deliveryDay', args: [] }, { op: 'const', name: 'val_5' }] },
          },
          {
            assertionId: 'clause_b', role: 'axiom',
            expr: { op: '>=', args: [{ op: 'call', symbol: 'deliveryDay', args: [] }, { op: 'const', name: 'val_10' }] },
          },
        ],
        queryPlan: { verificationMode: 'consistency', goal: { op: 'const', name: 'true_val' } },
        ambiguities: [],
        tags: ['contract', 'compliance'],
      },
    ],
    problems: [
      {
        prompt: 'Are these clauses compatible? Clause A: deliver within 5 days. Clause B: no delivery before day 10.',
        formalTarget: 'Constraint satisfiability over deliveryDay.',
        simulatedResult: {
          verdict: 'unsat',
          interpretation: 'inconsistent',
          reasoning: 'Clause A: deliveryDay ≤ 5.\nClause B: deliveryDay ≥ 10.\nNo integer satisfies both constraints simultaneously.\nThe system is unsatisfiable.',
          answer: 'The clauses are incompatible. No delivery date can satisfy both "within 5 days" and "not before day 10."',
          evidence: { unsatCoreIds: ['clause_a', 'clause_b'], verdict: 'unsat' },
        },
      },
    ],
  },

  {
    id: 'type-hierarchy',
    title: 'Ontology Subclass Reasoning',
    category: 'Ontology',
    description: 'Validates type assignments through a subclass chain. Demonstrates transitive implication reasoning.',
    knowledge: [
      {
        schemaVersion: V, proposalId: 'fp_onto_001', worldId: '_',
        source: src('type_defs', 50),
        declarations: [
          { kind: 'sort', name: 'Entity' },
          { kind: 'const', name: 'Penguin', resultSort: 'Entity' },
          { kind: 'predicate', name: 'isBird', argSorts: ['Entity'], resultSort: 'Bool' },
          { kind: 'predicate', name: 'isAnimal', argSorts: ['Entity'], resultSort: 'Bool' },
          { kind: 'predicate', name: 'isCompliant', argSorts: ['Entity'], resultSort: 'Bool' },
        ],
        assertions: [
          {
            assertionId: 'ax_bird_animal', role: 'axiom',
            expr: {
              op: 'forall', vars: [{ name: 'x', sort: 'Entity' }],
              body: { op: '=>', args: [
                { op: 'call', symbol: 'isBird', args: [{ op: 'var', name: 'x' }] },
                { op: 'call', symbol: 'isAnimal', args: [{ op: 'var', name: 'x' }] },
              ]},
            },
          },
          {
            assertionId: 'ax_animal_compliant', role: 'axiom',
            expr: {
              op: 'forall', vars: [{ name: 'x', sort: 'Entity' }],
              body: { op: '=>', args: [
                { op: 'call', symbol: 'isAnimal', args: [{ op: 'var', name: 'x' }] },
                { op: 'call', symbol: 'isCompliant', args: [{ op: 'var', name: 'x' }] },
              ]},
            },
          },
          {
            assertionId: 'fact_penguin', role: 'fact',
            expr: { op: 'call', symbol: 'isBird', args: [{ op: 'const', name: 'Penguin' }] },
          },
        ],
        queryPlan: { verificationMode: 'entailment', goal: { op: 'call', symbol: 'isCompliant', args: [{ op: 'const', name: 'Penguin' }] } },
        ambiguities: [],
        tags: ['ontology', 'classification'],
      },
    ],
    problems: [
      {
        prompt: 'Is Penguin compliant? Given: every Bird is an Animal, every Animal is compliant, Penguin is a Bird.',
        formalTarget: 'Two-step implication chain: isBird → isAnimal → isCompliant.',
        simulatedResult: {
          verdict: 'unsat',
          interpretation: 'entailed',
          reasoning: 'Chain: isBird(Penguin) → isAnimal(Penguin) → isCompliant(Penguin).\nFact: isBird(Penguin).\nFirst axiom fires: isAnimal(Penguin).\nSecond axiom fires: isCompliant(Penguin).\nRefutation of ¬isCompliant(Penguin) yields unsat.',
          answer: 'Yes, Penguin is compliant. The solver traced through the subclass chain: Bird → Animal → Compliant.',
          evidence: { fragmentIds: ['frag_00001', 'frag_00002', 'frag_00003'], unsatCoreIds: ['ax_bird_animal', 'ax_animal_compliant', 'fact_penguin'], verdict: 'unsat' },
        },
      },
    ],
  },
];
