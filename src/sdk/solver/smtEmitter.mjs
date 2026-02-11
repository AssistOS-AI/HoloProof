const DECLARATION_KIND_ORDER = new Map([
  ['sort', 0],
  ['const', 1],
  ['predicate', 2],
  ['function', 3],
]);

const IDENTIFIER_RE = /^[A-Za-z_][A-Za-z0-9_]*$/;
const RESERVED_PREFIXES = ['hp_internal_'];
const RESERVED_WORDS = new Set([
  'assert',
  'check-sat',
  'check_sat',
  'declare-const',
  'declare_const',
  'declare-fun',
  'declare_fun',
  'define-fun',
  'define_fun',
  'echo',
  'exit',
  'get-model',
  'get_model',
  'get-unsat-core',
  'get_unsat_core',
  'let',
  'pop',
  'push',
  'reset',
  'set-logic',
  'set_logic',
  'set-option',
  'set_option',
]);

function assertIdentifier(value, label) {
  const text = String(value || '');
  if (!IDENTIFIER_RE.test(text)) {
    throw new Error(`${label} must match ${IDENTIFIER_RE}.`);
  }
  const normalized = text.toLowerCase();
  if (RESERVED_WORDS.has(normalized)) {
    throw new Error(`${label} cannot use reserved solver identifier "${text}".`);
  }
  if (RESERVED_PREFIXES.some((prefix) => normalized.startsWith(prefix))) {
    throw new Error(`${label} cannot use reserved prefix.`);
  }
  return text;
}

function operatorToken(op) {
  const map = {
    and: 'and',
    or: 'or',
    not: 'not',
    '=>': '=>',
    '=': '=',
    '>': '>',
    '>=': '>=',
    '<': '<',
    '<=': '<=',
    '+': '+',
    '-': '-',
    '*': '*',
    '/': '/',
    distinct: 'distinct',
    ite: 'ite',
    forall: 'forall',
    exists: 'exists',
  };

  if (!map[op]) {
    throw new Error(`Unsupported expression operator for SMT emission: ${op}`);
  }

  return map[op];
}

function renderExpr(expr) {
  if (!expr || typeof expr !== 'object') {
    throw new Error('Expression must be an object.');
  }

  switch (expr.op) {
    case 'const':
    case 'var':
      return assertIdentifier(expr.name, `${expr.op}.name`);
    case 'call': {
      const symbol = assertIdentifier(expr.symbol, 'call.symbol');
      const args = Array.isArray(expr.args) ? expr.args.map((arg) => renderExpr(arg)) : [];
      return `(${symbol}${args.length ? ` ${args.join(' ')}` : ''})`;
    }
    case 'not':
      return `(not ${renderExpr(expr.arg)})`;
    case 'forall':
    case 'exists': {
      const vars = Array.isArray(expr.vars)
        ? expr.vars.map((bound) => `(${assertIdentifier(bound.name, 'bound variable')} ${assertIdentifier(bound.sort, 'bound sort')})`).join(' ')
        : '';
      return `(${operatorToken(expr.op)} (${vars}) ${renderExpr(expr.body)})`;
    }
    default: {
      const op = operatorToken(expr.op);
      const args = Array.isArray(expr.args) ? expr.args.map((arg) => renderExpr(arg)) : [];
      if (args.length === 0) {
        throw new Error(`Operator "${expr.op}" requires at least one argument.`);
      }
      return `(${op} ${args.join(' ')})`;
    }
  }
}

export function emitExpressionSmt(expr) {
  return renderExpr(expr);
}

export function emitDeclarationSmt(declaration) {
  if (!declaration || typeof declaration !== 'object') {
    throw new Error('Declaration must be an object.');
  }

  const name = assertIdentifier(declaration.name, 'declaration.name');

  switch (declaration.kind) {
    case 'sort':
      return `(declare-sort ${name} 0)`;
    case 'const':
      return `(declare-const ${name} ${assertIdentifier(declaration.resultSort, 'const.resultSort')})`;
    case 'predicate':
    case 'function': {
      const argSorts = Array.isArray(declaration.argSorts)
        ? declaration.argSorts.map((sortName) => assertIdentifier(sortName, 'declaration.argSort')).join(' ')
        : '';
      const resultSort = assertIdentifier(declaration.resultSort, 'declaration.resultSort');
      return `(declare-fun ${name} (${argSorts}) ${resultSort})`;
    }
    default:
      throw new Error(`Unsupported declaration kind for SMT emission: ${declaration.kind}`);
  }
}

export function emitAssertionSmt(assertion, options = {}) {
  if (!assertion || typeof assertion !== 'object') {
    throw new Error('Assertion must be an object.');
  }

  const exprText = emitExpressionSmt(assertion.expr);

  if (options.named !== false && assertion.assertionId) {
    const assertionId = assertIdentifier(assertion.assertionId, 'assertion.assertionId');
    return `(assert (! ${exprText} :named ${assertionId}))`;
  }

  return `(assert ${exprText})`;
}

export function sortDeclarationsForEmission(declarations) {
  return [...declarations].sort((left, right) => {
    const leftRank = DECLARATION_KIND_ORDER.get(left.kind) ?? 99;
    const rightRank = DECLARATION_KIND_ORDER.get(right.kind) ?? 99;

    if (leftRank !== rightRank) {
      return leftRank - rightRank;
    }

    return String(left.name).localeCompare(String(right.name));
  });
}

export function emitProposalSmtStatements(proposal, options = {}) {
  const lines = [];

  if (typeof proposal?.logic === 'string' && proposal.logic.trim()) {
    lines.push(`(set-logic ${proposal.logic.trim()})`);
  }

  const declarations = sortDeclarationsForEmission(proposal.declarations || []);
  for (const declaration of declarations) {
    lines.push(emitDeclarationSmt(declaration));
  }

  for (const assertion of proposal.assertions || []) {
    lines.push(emitAssertionSmt(assertion, { named: options.namedAssertions !== false }));
  }

  if (options.includeGoal === true && proposal.queryPlan?.goal) {
    const goalAssertionId = options.goalAssertionId || 'query_goal';
    lines.push(emitAssertionSmt({ assertionId: goalAssertionId, expr: proposal.queryPlan.goal }, { named: true }));
  }

  return lines;
}

export function emitNegatedGoalAssertion(goalExpr, assertionId = 'query_negated_goal') {
  return emitAssertionSmt({
    assertionId,
    expr: {
      op: 'not',
      arg: goalExpr,
    },
  }, { named: true });
}

export function emitProposalSmtScript(proposal, options = {}) {
  const statements = emitProposalSmtStatements(proposal, options);
  if (options.includeCheckSat !== false) {
    statements.push('(check-sat)');
  }
  if (options.includeModel === true) {
    statements.push('(get-model)');
  }
  if (options.includeUnsatCore === true) {
    statements.push('(get-unsat-core)');
  }
  return statements.join('\n');
}
