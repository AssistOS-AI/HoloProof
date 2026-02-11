export const IDENTIFIER_RE = /^[A-Za-z_][A-Za-z0-9_]*$/;

const RESERVED_IDENTIFIER_WORDS = new Set([
  'assert',
  'check_sat',
  'declare_const',
  'declare_fun',
  'define_fun',
  'echo',
  'exit',
  'get_model',
  'get_unsat_core',
  'let',
  'pop',
  'push',
  'set_logic',
  'set_option',
]);

export const FORMAL_PROPOSAL_SCHEMA_VERSION = 'holoproof.formal-proposal.v1';

export const ALLOWED_EXPR_OPS = new Set([
  'const',
  'var',
  'call',
  'not',
  'and',
  'or',
  '=>',
  '=',
  '>',
  '>=',
  '<',
  '<=',
  '+',
  '-',
  '*',
  '/',
  'forall',
  'exists',
]);

export function validateFormalProposal(proposal) {
  const errors = [];

  if (!isRecord(proposal)) {
    return { valid: false, errors: ['Proposal must be an object.'] };
  }

  requireStringField(proposal, 'schemaVersion', errors);
  if (proposal.schemaVersion !== FORMAL_PROPOSAL_SCHEMA_VERSION) {
    errors.push(`schemaVersion must be "${FORMAL_PROPOSAL_SCHEMA_VERSION}".`);
  }

  requireStringField(proposal, 'proposalId', errors, isIdentifier);
  requireStringField(proposal, 'worldId', errors, isIdentifier);

  validateSource(proposal.source, errors);
  validateDeclarations(proposal.declarations, errors);
  validateAssertions(proposal.assertions, errors);
  validateQueryPlan(proposal.queryPlan, errors);
  validateAmbiguities(proposal.ambiguities, errors);
  validateTags(proposal.tags, errors);

  return { valid: errors.length === 0, errors };
}

export function collectReferencedSymbols(expression) {
  const symbols = new Set();

  walkExpr(expression, (node) => {
    if (node.op === 'call' && typeof node.symbol === 'string' && node.symbol) {
      symbols.add(node.symbol);
    }
    if (node.op === 'const' && typeof node.name === 'string' && node.name) {
      symbols.add(node.name);
    }
  });

  return [...symbols];
}

function validateSource(source, errors) {
  if (!isRecord(source)) {
    errors.push('source must be an object.');
    return;
  }

  requireStringField(source, 'sourceId', errors);

  if (!isRecord(source.span)) {
    errors.push('source.span must be an object with start/end.');
  } else {
    if (!Number.isInteger(source.span.start) || source.span.start < 0) {
      errors.push('source.span.start must be a non-negative integer.');
    }
    if (!Number.isInteger(source.span.end) || source.span.end < source.span.start) {
      errors.push('source.span.end must be an integer >= source.span.start.');
    }
  }

  if (typeof source.createdAt !== 'string' || !source.createdAt.trim()) {
    errors.push('source.createdAt must be a non-empty ISO timestamp string.');
  } else if (!Number.isFinite(Date.parse(source.createdAt))) {
    errors.push('source.createdAt must be a parseable timestamp.');
  }
}

function validateDeclarations(declarations, errors) {
  if (!Array.isArray(declarations)) {
    errors.push('declarations must be an array.');
    return;
  }

  for (let i = 0; i < declarations.length; i += 1) {
    const decl = declarations[i];
    const prefix = `declarations[${i}]`;

    if (!isRecord(decl)) {
      errors.push(`${prefix} must be an object.`);
      continue;
    }

    const allowedKinds = new Set(['sort', 'const', 'predicate', 'function']);
    if (!allowedKinds.has(decl.kind)) {
      errors.push(`${prefix}.kind must be one of: sort, const, predicate, function.`);
    }

    if (!isIdentifier(decl.name)) {
      errors.push(`${prefix}.name must be an identifier.`);
    }

    if (decl.kind === 'predicate' || decl.kind === 'function') {
      if (!Array.isArray(decl.argSorts)) {
        errors.push(`${prefix}.argSorts must be an array.`);
      } else {
        for (let j = 0; j < decl.argSorts.length; j += 1) {
          if (!isSortName(decl.argSorts[j])) {
            errors.push(`${prefix}.argSorts[${j}] must be a valid sort name.`);
          }
        }
      }

      if (!isSortName(decl.resultSort)) {
        errors.push(`${prefix}.resultSort must be a valid sort name.`);
      }

      if (decl.kind === 'predicate' && decl.resultSort !== 'Bool') {
        errors.push(`${prefix}.resultSort must be Bool for predicate declarations.`);
      }
    }

    if (decl.kind === 'const') {
      if (!isSortName(decl.resultSort)) {
        errors.push(`${prefix}.resultSort must be present for const declarations.`);
      }
    }
  }
}

function validateAssertions(assertions, errors) {
  if (!Array.isArray(assertions)) {
    errors.push('assertions must be an array.');
    return;
  }

  const allowedRoles = new Set(['axiom', 'fact', 'assumption', 'query']);

  for (let i = 0; i < assertions.length; i += 1) {
    const assertion = assertions[i];
    const prefix = `assertions[${i}]`;

    if (!isRecord(assertion)) {
      errors.push(`${prefix} must be an object.`);
      continue;
    }

    if (!isIdentifier(assertion.assertionId)) {
      errors.push(`${prefix}.assertionId must be an identifier.`);
    }

    if (!allowedRoles.has(assertion.role)) {
      errors.push(`${prefix}.role must be one of: axiom, fact, assumption, query.`);
    }

    validateExpr(assertion.expr, `${prefix}.expr`, errors);
  }
}

function validateQueryPlan(queryPlan, errors) {
  if (!isRecord(queryPlan)) {
    errors.push('queryPlan must be an object.');
    return;
  }

  const modes = new Set(['entailment', 'model-finding', 'consistency']);
  if (!modes.has(queryPlan.verificationMode)) {
    errors.push('queryPlan.verificationMode must be entailment, model-finding, or consistency.');
  }

  validateExpr(queryPlan.goal, 'queryPlan.goal', errors);
}

function validateAmbiguities(ambiguities, errors) {
  if (!Array.isArray(ambiguities)) {
    errors.push('ambiguities must be an array.');
    return;
  }

  for (let i = 0; i < ambiguities.length; i += 1) {
    const item = ambiguities[i];
    if (typeof item !== 'string' && !isRecord(item)) {
      errors.push(`ambiguities[${i}] must be a string or object.`);
    }
  }
}

function validateTags(tags, errors) {
  if (!Array.isArray(tags)) {
    errors.push('tags must be an array.');
    return;
  }

  for (let i = 0; i < tags.length; i += 1) {
    if (typeof tags[i] !== 'string' || !tags[i].trim()) {
      errors.push(`tags[${i}] must be a non-empty string.`);
    }
  }
}

function validateExpr(expr, path, errors) {
  if (!isRecord(expr)) {
    errors.push(`${path} must be an object.`);
    return;
  }

  if (!ALLOWED_EXPR_OPS.has(expr.op)) {
    errors.push(`${path}.op "${expr.op}" is not supported.`);
    return;
  }

  switch (expr.op) {
    case 'const':
      if (!isIdentifier(expr.name)) {
        errors.push(`${path}.name must be an identifier for const.`);
      }
      return;
    case 'var':
      if (!isIdentifier(expr.name)) {
        errors.push(`${path}.name must be an identifier for var.`);
      }
      return;
    case 'call':
      if (!isIdentifier(expr.symbol)) {
        errors.push(`${path}.symbol must be an identifier for call.`);
      }
      if (!Array.isArray(expr.args)) {
        errors.push(`${path}.args must be an array for call.`);
        return;
      }
      for (let i = 0; i < expr.args.length; i += 1) {
        validateExpr(expr.args[i], `${path}.args[${i}]`, errors);
      }
      return;
    case 'forall':
    case 'exists':
      if (!Array.isArray(expr.vars) || expr.vars.length === 0) {
        errors.push(`${path}.vars must be a non-empty array for quantifiers.`);
      } else {
        for (let i = 0; i < expr.vars.length; i += 1) {
          const boundVar = expr.vars[i];
          if (!isRecord(boundVar) || !isIdentifier(boundVar.name) || !isSortName(boundVar.sort)) {
            errors.push(`${path}.vars[${i}] must include valid name and sort.`);
          }
        }
      }
      validateExpr(expr.body, `${path}.body`, errors);
      return;
    case 'not':
      validateExpr(expr.arg, `${path}.arg`, errors);
      return;
    default:
      if (!Array.isArray(expr.args) || expr.args.length === 0) {
        errors.push(`${path}.args must be a non-empty array for operator ${expr.op}.`);
        return;
      }
      for (let i = 0; i < expr.args.length; i += 1) {
        validateExpr(expr.args[i], `${path}.args[${i}]`, errors);
      }
  }
}

function walkExpr(expr, visitor) {
  if (!isRecord(expr)) {
    return;
  }

  visitor(expr);

  if (Array.isArray(expr.args)) {
    for (const arg of expr.args) {
      walkExpr(arg, visitor);
    }
  }

  if (isRecord(expr.body)) {
    walkExpr(expr.body, visitor);
  }

  if (isRecord(expr.arg)) {
    walkExpr(expr.arg, visitor);
  }
}

function requireStringField(obj, key, errors, validator = null) {
  if (typeof obj[key] !== 'string' || !obj[key].trim()) {
    errors.push(`${key} must be a non-empty string.`);
    return;
  }

  if (validator && !validator(obj[key])) {
    errors.push(`${key} has invalid value "${obj[key]}".`);
  }
}

function isSortName(value) {
  return isIdentifier(value);
}

function isIdentifier(value) {
  if (typeof value !== 'string') {
    return false;
  }
  if (!IDENTIFIER_RE.test(value)) {
    return false;
  }
  return !RESERVED_IDENTIFIER_WORDS.has(value.toLowerCase());
}

function isRecord(value) {
  return value !== null && typeof value === 'object' && !Array.isArray(value);
}
