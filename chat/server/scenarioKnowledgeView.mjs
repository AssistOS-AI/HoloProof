function formatConstName(name) {
  const raw = String(name || '?').trim();
  const match = raw.match(/^val_(-?\d+)$/);
  if (match) {
    return match[1];
  }
  return raw || '?';
}

function symbolToWords(symbol) {
  const raw = String(symbol || '').trim();
  if (!raw) {
    return 'value';
  }

  let text = raw.replace(/_/g, ' ');
  text = text.replace(/([a-z0-9])([A-Z])/g, '$1 $2');
  text = text.toLowerCase();

  if (text.startsWith('is ') && text.length > 3) {
    return text.slice(3);
  }
  return text;
}

function normalizeSentence(text) {
  const trimmed = String(text || '').replace(/\s+/g, ' ').trim();
  if (!trimmed) {
    return '';
  }
  const withPeriod = /[.!?]$/.test(trimmed) ? trimmed : `${trimmed}.`;
  return withPeriod.charAt(0).toUpperCase() + withPeriod.slice(1);
}

function startsWithModalPhrase(phrase) {
  return [
    'can ',
    'must ',
    'should ',
    'may ',
    'has ',
    'have ',
    'needs ',
    'need ',
  ].some((prefix) => phrase.startsWith(prefix));
}

function indefiniteArticle(noun) {
  const text = String(noun || '').trim();
  if (!text) {
    return 'a';
  }
  const lower = text.toLowerCase();
  if (lower.startsWith('user') || lower.startsWith('uni') || lower.startsWith('euro') || lower.startsWith('one')) {
    return 'a';
  }
  return /^[aeiou]/i.test(text) ? 'an' : 'a';
}

function renderTerm(expr) {
  if (!expr || typeof expr !== 'object') {
    return 'something';
  }

  if (expr.op === 'const') {
    return formatConstName(expr.name);
  }

  if (expr.op === 'var') {
    return String(expr.name || 'x');
  }

  if (expr.op === 'call') {
    const phrase = symbolToWords(expr.symbol);
    const args = Array.isArray(expr.args) ? expr.args.map((arg) => renderTerm(arg)) : [];
    if (args.length === 0) {
      return phrase;
    }
    if (args.length === 1) {
      return `${phrase} of ${args[0]}`;
    }
    return `${phrase}(${args.join(', ')})`;
  }

  return renderFormula(expr);
}

function renderPredicateCall(expr) {
  const phrase = symbolToWords(expr.symbol);
  const args = Array.isArray(expr.args) ? expr.args.map((arg) => renderTerm(arg)) : [];

  if (args.length === 0) {
    return phrase;
  }

  if (args.length === 1) {
    if (startsWithModalPhrase(phrase)) {
      return `${args[0]} ${phrase}`;
    }
    return `${args[0]} is ${phrase}`;
  }

  if (args.length === 2) {
    if (phrase === 'edge') {
      return `${args[0]} is connected to ${args[1]}`;
    }
    if (phrase === 'blocked') {
      return `the connection from ${args[0]} to ${args[1]} is blocked`;
    }
    if (phrase === 'reachable') {
      return `${args[0]} can reach ${args[1]}`;
    }
    if (phrase === 'overlaps') {
      return `${args[0]} overlaps with ${args[1]}`;
    }
    if (phrase.endsWith(' of')) {
      return `${args[0]} is ${phrase} ${args[1]}`;
    }
    if (startsWithModalPhrase(phrase)) {
      return `${args[0]} ${phrase} ${args[1]}`;
    }
    return `${args[0]} ${phrase} ${args[1]}`;
  }

  return `${phrase}(${args.join(', ')})`;
}

function renderFormula(expr) {
  if (!expr || typeof expr !== 'object') {
    return 'something is stated';
  }

  switch (expr.op) {
    case 'call':
      return renderPredicateCall(expr);
    case 'not':
      return `it is not true that ${renderFormula(expr.arg)}`;
    case 'and': {
      const args = Array.isArray(expr.args) ? expr.args.map((arg) => renderFormula(arg)) : [];
      return args.join(' and ');
    }
    case 'or': {
      const args = Array.isArray(expr.args) ? expr.args.map((arg) => renderFormula(arg)) : [];
      return args.join(' or ');
    }
    case '=>': {
      const args = Array.isArray(expr.args) ? expr.args : [];
      if (args.length < 2) {
        return 'an implication is stated';
      }
      return `if ${renderFormula(args[0])}, then ${renderFormula(args[1])}`;
    }
    case '=': {
      const args = Array.isArray(expr.args) ? expr.args : [];
      if (args.length < 2) {
        return 'an equality is stated';
      }
      return `${renderTerm(args[0])} equals ${renderTerm(args[1])}`;
    }
    case '<':
    case '<=':
    case '>':
    case '>=': {
      const args = Array.isArray(expr.args) ? expr.args : [];
      if (args.length < 2) {
        return 'a comparison is stated';
      }
      const label = {
        '<': 'is less than',
        '<=': 'is less than or equal to',
        '>': 'is greater than',
        '>=': 'is greater than or equal to',
      }[expr.op];
      return `${renderTerm(args[0])} ${label} ${renderTerm(args[1])}`;
    }
    case 'forall':
    case 'exists': {
      const vars = Array.isArray(expr.vars)
        ? expr.vars.map((item) => `${item.name} of type ${item.sort}`).join(', ')
        : 'some variable';
      const quantifier = expr.op === 'forall' ? 'for every' : 'there exists';
      return `${quantifier} ${vars}, ${renderFormula(expr.body)}`;
    }
    default:
      return `${String(expr.op || 'expression')} is stated`;
  }
}

function formatConstDeclaration(declaration) {
  if (declaration?.kind !== 'const') {
    return '';
  }
  const name = String(declaration.name || '').trim();
  const sort = String(declaration.resultSort || '').trim();
  if (!name || !sort || /^val_(-?\d+)$/.test(name)) {
    return '';
  }
  return normalizeSentence(`${name} is ${indefiniteArticle(sort)} ${sort}`);
}

function formatAssertion(assertion) {
  return normalizeSentence(renderFormula(assertion?.expr));
}

export function buildKnowledgeSummary(scenario) {
  return scenario.knowledge.reduce((acc, item) => {
    acc.proposals += 1;
    acc.declarations += Array.isArray(item.declarations) ? item.declarations.length : 0;
    acc.assertions += Array.isArray(item.assertions) ? item.assertions.length : 0;
    return acc;
  }, {
    proposals: 0,
    declarations: 0,
    assertions: 0,
  });
}

export function buildKnowledgePreview(scenario) {
  const seen = new Set();
  const preview = [];

  function pushLine(text) {
    const line = String(text || '').trim();
    if (!line || seen.has(line)) {
      return;
    }
    seen.add(line);
    preview.push(line);
  }

  for (let i = 0; i < scenario.knowledge.length; i += 1) {
    const proposal = scenario.knowledge[i];

    for (const declaration of proposal.declarations || []) {
      pushLine(formatConstDeclaration(declaration));
    }

    for (const assertion of proposal.assertions || []) {
      pushLine(formatAssertion(assertion));
    }
  }

  if (preview.length === 0) {
    preview.push('No explicit facts or rules are available for this scenario.');
  }

  return preview;
}
