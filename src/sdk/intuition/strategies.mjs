const DEFAULT_DIM = 256;
const DEFAULT_TOP_K = 50;

function positiveInteger(value, fallback) {
  return Number.isInteger(value) && value > 0 ? value : fallback;
}

function hash32(input) {
  let hash = 2166136261;
  const text = String(input ?? '');
  for (let i = 0; i < text.length; i += 1) {
    hash ^= text.charCodeAt(i);
    hash = Math.imul(hash, 16777619);
  }
  return hash >>> 0;
}

function tokenize(text) {
  return String(text ?? '')
    .toLowerCase()
    .split(/[^a-z0-9_]+/)
    .filter(Boolean);
}

function exprTokens(expr, path = 'root', out = []) {
  if (!expr || typeof expr !== 'object') {
    return out;
  }

  if (typeof expr.op === 'string') {
    out.push(`op:${expr.op}@${path}`);
  }
  if (typeof expr.symbol === 'string') {
    out.push(`sym:${expr.symbol}@${path}`);
  }
  if (typeof expr.name === 'string') {
    out.push(`name:${expr.name}@${path}`);
  }

  if (Array.isArray(expr.args)) {
    for (let i = 0; i < expr.args.length; i += 1) {
      exprTokens(expr.args[i], `${path}.arg${i}`, out);
    }
  }

  if (Array.isArray(expr.vars)) {
    for (let i = 0; i < expr.vars.length; i += 1) {
      const bound = expr.vars[i];
      if (bound && typeof bound === 'object') {
        out.push(`bound:${bound.name || ''}:${bound.sort || ''}@${path}.var${i}`);
      }
    }
  }

  if (expr.body && typeof expr.body === 'object') {
    exprTokens(expr.body, `${path}.body`, out);
  }

  if (expr.arg && typeof expr.arg === 'object') {
    exprTokens(expr.arg, `${path}.arg`, out);
  }

  return out;
}

function fragmentTokens(fragment) {
  const bag = [];
  bag.push(...tokenize(fragment.fragmentId || ''));
  bag.push(...tokenize(fragment.assertionId || ''));
  bag.push(...tokenize(fragment.role || ''));
  bag.push(...exprTokens(fragment.expr || {}));
  return bag;
}

function queryTokens(queryContext = {}) {
  const bag = [];
  bag.push(...tokenize(queryContext.queryText || ''));
  bag.push(...exprTokens(queryContext.goal || {}));
  bag.push(...tokenize(queryContext.verificationMode || ''));
  return bag;
}

function circularConvolution(left, right) {
  const dim = left.length;
  const out = new Float32Array(dim);
  for (let i = 0; i < dim; i += 1) {
    let sum = 0;
    for (let j = 0; j < dim; j += 1) {
      const k = (i - j + dim) % dim;
      sum += left[j] * right[k];
    }
    out[i] = sum;
  }
  return out;
}

function normalizeDense(vector) {
  let norm = 0;
  for (let i = 0; i < vector.length; i += 1) {
    norm += vector[i] * vector[i];
  }
  norm = Math.sqrt(norm);
  if (norm <= 0) {
    return vector;
  }
  for (let i = 0; i < vector.length; i += 1) {
    vector[i] /= norm;
  }
  return vector;
}

function cosineSimilarity(left, right) {
  let dot = 0;
  for (let i = 0; i < left.length; i += 1) {
    dot += left[i] * right[i];
  }
  return dot;
}

function denseTokenVector(token, dim) {
  const vector = new Float32Array(dim);
  const seed = hash32(token);
  const step = (hash32(`${token}:step`) % dim) || 1;
  const projections = 8;
  for (let i = 0; i < projections; i += 1) {
    const idx = (seed + i * step) % dim;
    vector[idx] += (hash32(`${token}:sgn:${i}`) & 1) ? 1 : -1;
  }
  return normalizeDense(vector);
}

function roleDenseVector(roleName, dim) {
  return denseTokenVector(`role:${roleName}`, dim);
}

function encodeDenseWithRoles(tokens, options = {}) {
  const dim = positiveInteger(options.dim, DEFAULT_DIM);
  const output = new Float32Array(dim);

  for (const token of tokens) {
    const parts = token.split('@');
    const semanticToken = parts[0];
    const path = parts[1] || 'root';
    const role = path.includes('.arg')
      ? `arg_${path.split('.arg').at(-1).split('.')[0]}`
      : path.includes('.body')
        ? 'body'
        : path.includes('.var')
          ? 'bound'
          : 'pred';

    const bound = circularConvolution(
      roleDenseVector(role, dim),
      denseTokenVector(semanticToken, dim),
    );

    for (let i = 0; i < output.length; i += 1) {
      output[i] += bound[i];
    }
  }

  return normalizeDense(output);
}

function binaryTokenVector(token, dim) {
  const out = new Uint8Array(dim);
  const seed = hash32(token);
  const step = (hash32(`${token}:step`) % dim) || 1;
  for (let i = 0; i < dim; i += 1) {
    const idx = (seed + i * step) % dim;
    out[idx] = hash32(`${token}:bit:${i}`) & 1;
  }
  return out;
}

function xorVectors(left, right) {
  const out = new Uint8Array(left.length);
  for (let i = 0; i < out.length; i += 1) {
    out[i] = left[i] ^ right[i];
  }
  return out;
}

function bundleBinary(vectors, tieBreaker = 0) {
  if (vectors.length === 0) {
    return new Uint8Array(0);
  }
  const dim = vectors[0].length;
  const out = new Uint8Array(dim);
  for (let i = 0; i < dim; i += 1) {
    let ones = 0;
    for (const vector of vectors) {
      ones += vector[i] === 1 ? 1 : 0;
    }
    const zeros = vectors.length - ones;
    if (ones > zeros) {
      out[i] = 1;
    } else if (ones < zeros) {
      out[i] = 0;
    } else {
      out[i] = tieBreaker;
    }
  }
  return out;
}

function roleBinaryVector(roleName, dim) {
  return binaryTokenVector(`role:${roleName}`, dim);
}

function encodeBinaryWithRoles(tokens, options = {}) {
  const dim = positiveInteger(options.dim, DEFAULT_DIM);
  const boundVectors = [];

  for (const token of tokens) {
    const parts = token.split('@');
    const semanticToken = parts[0];
    const path = parts[1] || 'root';
    const role = path.includes('.arg')
      ? `arg_${path.split('.arg').at(-1).split('.')[0]}`
      : path.includes('.body')
        ? 'body'
        : path.includes('.var')
          ? 'bound'
          : 'pred';

    const roleVec = roleBinaryVector(role, dim);
    const tokenVec = binaryTokenVector(semanticToken, dim);
    boundVectors.push(xorVectors(roleVec, tokenVec));
  }

  const tieBreaker = hash32(tokens.join('|')) & 1;
  return bundleBinary(boundVectors, tieBreaker);
}

function hammingSimilarity(left, right) {
  if (!left || !right || left.length !== right.length || left.length === 0) {
    return 0;
  }
  let equal = 0;
  for (let i = 0; i < left.length; i += 1) {
    if (left[i] === right[i]) {
      equal += 1;
    }
  }
  return equal / left.length;
}

function sortRows(rows) {
  rows.sort((a, b) => {
    if (b.score !== a.score) {
      return b.score - a.score;
    }
    return a.fragmentId.localeCompare(b.fragmentId);
  });
  return rows;
}

export class NoIntuitionStrategy {
  constructor(options = {}) {
    this._lastDiagnostics = {
      strategy: 'no-intuition',
      reason: 'heuristic ranking disabled',
      selectedCount: 0,
    };
    this._options = options;
  }

  prepare(worldSnapshot = null) {
    this._lastDiagnostics = {
      strategy: 'no-intuition',
      reason: 'heuristic ranking disabled',
      worldId: worldSnapshot?.worldId || null,
      selectedCount: 0,
    };
  }

  selectCandidates(queryContext, kbFragments, budget = {}) {
    const topK = positiveInteger(budget.topK, DEFAULT_TOP_K);
    const selected = (kbFragments || [])
      .slice()
      .sort((left, right) => String(left.fragmentId).localeCompare(String(right.fragmentId)))
      .slice(0, topK);

    this._lastDiagnostics = {
      strategy: 'no-intuition',
      reason: 'heuristic ranking disabled',
      queryTokens: queryTokens(queryContext),
      selectedCount: selected.length,
    };

    return selected.map((fragment, index) => ({
      fragmentId: fragment.fragmentId,
      score: selected.length - index,
      metadata: { reason: 'deterministic-order' },
    }));
  }

  explainSelection() {
    return { ...this._lastDiagnostics };
  }
}

export class VSAIntuitionStrategy {
  constructor(options = {}) {
    this._representation = options.representation || 'vsa-hrr-cosine-topk';
    this._dim = positiveInteger(options.dim, DEFAULT_DIM);
    this._index = new Map();
    this._lastDiagnostics = {
      strategy: 'vsa-intuition',
      representation: this._representation,
      selectedCount: 0,
    };
  }

  prepare(worldSnapshot = null) {
    this._index.clear();
    const fragments = Array.isArray(worldSnapshot?.fragments) ? worldSnapshot.fragments : [];
    for (const fragment of fragments) {
      this._index.set(fragment.fragmentId, this._encodeFragment(fragment));
    }

    this._lastDiagnostics = {
      strategy: 'vsa-intuition',
      representation: this._representation,
      indexedFragments: this._index.size,
      selectedCount: 0,
    };
  }

  _encodeFragment(fragment) {
    const tokens = fragmentTokens(fragment);
    if (this._representation === 'vsa-hdc-binary-hamming-topk') {
      return {
        family: 'hdc-binary',
        tokens,
        vector: encodeBinaryWithRoles(tokens, { dim: this._dim }),
      };
    }

    return {
      family: 'hrr',
      tokens,
      vector: encodeDenseWithRoles(tokens, { dim: this._dim }),
    };
  }

  _encodeQuery(queryContext) {
    const tokens = queryTokens(queryContext);
    if (this._representation === 'vsa-hdc-binary-hamming-topk') {
      return {
        family: 'hdc-binary',
        tokens,
        vector: encodeBinaryWithRoles(tokens, { dim: this._dim }),
      };
    }
    return {
      family: 'hrr',
      tokens,
      vector: encodeDenseWithRoles(tokens, { dim: this._dim }),
    };
  }

  selectCandidates(queryContext, kbFragments, budget = {}) {
    const topK = positiveInteger(budget.topK, DEFAULT_TOP_K);
    const query = this._encodeQuery(queryContext || {});
    const rows = [];

    for (const fragment of kbFragments || []) {
      const encoded = this._index.get(fragment.fragmentId) || this._encodeFragment(fragment);
      this._index.set(fragment.fragmentId, encoded);

      let score = 0;
      if (encoded.family === 'hdc-binary') {
        score = hammingSimilarity(query.vector, encoded.vector);
      } else {
        score = cosineSimilarity(query.vector, encoded.vector);
      }

      rows.push({
        fragmentId: fragment.fragmentId,
        score,
        metadata: {
          family: encoded.family,
          tokenCount: encoded.tokens.length,
        },
      });
    }

    const ranked = sortRows(rows).slice(0, topK);

    this._lastDiagnostics = {
      strategy: 'vsa-intuition',
      representation: this._representation,
      queryTokens: query.tokens,
      selectedCount: ranked.length,
      topScore: ranked[0]?.score ?? null,
      bottomScore: ranked.length ? ranked[ranked.length - 1].score : null,
    };

    return ranked;
  }

  explainSelection() {
    return { ...this._lastDiagnostics };
  }
}

export function createIntuitionStrategy(config = {}) {
  const strategy = String(config.strategy || 'no-intuition');
  if (strategy === 'vsa-intuition') {
    return new VSAIntuitionStrategy({
      representation: config.representation || 'vsa-hrr-cosine-topk',
      dim: config.dim,
    });
  }
  return new NoIntuitionStrategy();
}

