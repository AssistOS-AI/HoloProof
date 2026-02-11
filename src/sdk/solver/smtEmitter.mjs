const DECLARATION_KIND_ORDER = new Map([
  ['sort', 0],
  ['const', 1],
  ['predicate', 2],
  ['function', 3],
]);

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
      return String(expr.name);
    case 'call': {
      const args = Array.isArray(expr.args) ? expr.args.map((arg) => renderExpr(arg)) : [];
      return `(${expr.symbol}${args.length ? ` ${args.join(' ')}` : ''})`;
    }
    case 'not':
      return `(not ${renderExpr(expr.arg)})`;
    case 'forall':
    case 'exists': {
      const vars = Array.isArray(expr.vars)
        ? expr.vars.map((bound) => `(${bound.name} ${bound.sort})`).join(' ')
        : '';
      return `(${operatorToken(expr.op)} (${vars}) ${renderExpr(expr.body)})`;
    }
    default: {
      const op = operatorToken(expr.op);
      const args = Array.isArray(expr.args) ? expr.args.map((arg) => renderExpr(arg)) : [];
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

  switch (declaration.kind) {
    case 'sort':
      return `(declare-sort ${declaration.name} 0)`;
    case 'const':
      return `(declare-const ${declaration.name} ${declaration.resultSort})`;
    case 'predicate':
    case 'function': {
      const argSorts = Array.isArray(declaration.argSorts) ? declaration.argSorts.join(' ') : '';
      return `(declare-fun ${declaration.name} (${argSorts}) ${declaration.resultSort})`;
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
    return `(assert (! ${exprText} :named ${assertion.assertionId}))`;
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
