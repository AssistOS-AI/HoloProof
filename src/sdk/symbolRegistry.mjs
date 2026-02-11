function canonicalizeDeclaration(declaration, declaredIn) {
  const kind = declaration.kind;
  const symbol = declaration.name;
  const semanticHint = typeof declaration.semanticHint === 'string' && declaration.semanticHint.trim()
    ? declaration.semanticHint.trim()
    : null;

  const base = {
    symbol,
    kind,
    semanticHint,
    usageCount: Number.isInteger(declaration.usageCount) && declaration.usageCount >= 0
      ? declaration.usageCount
      : 0,
    declaredIn,
    status: 'active',
  };

  if (kind === 'sort') {
    return {
      ...base,
      arity: 0,
      argSorts: [],
      resultSort: declaration.name,
    };
  }

  if (kind === 'const') {
    return {
      ...base,
      arity: 0,
      argSorts: [],
      resultSort: declaration.resultSort,
    };
  }

  return {
    ...base,
    arity: Array.isArray(declaration.argSorts) ? declaration.argSorts.length : 0,
    argSorts: Array.isArray(declaration.argSorts) ? declaration.argSorts.slice() : [],
    resultSort: declaration.resultSort,
  };
}

function structuralKey(entry, resolveSort) {
  return JSON.stringify({
    symbol: entry.symbol,
    kind: entry.kind,
    arity: entry.arity,
    argSorts: entry.argSorts.map((sort) => resolveSort(sort)),
    resultSort: resolveSort(entry.resultSort),
  });
}

function normalizeName(name) {
  return String(name || '').toLowerCase().replaceAll(/[^a-z0-9]/g, '');
}

function tokenize(text) {
  return String(text || '')
    .toLowerCase()
    .split(/[^a-z0-9]+/)
    .filter(Boolean);
}

function overlapScore(tokensA, tokensB) {
  const left = new Set(tokensA);
  let count = 0;
  for (const token of tokensB) {
    if (left.has(token)) {
      count += 1;
    }
  }
  return count;
}

function hashString(input) {
  let hash = 2166136261;
  const text = String(input);
  for (let i = 0; i < text.length; i += 1) {
    hash ^= text.charCodeAt(i);
    hash = Math.imul(hash, 16777619);
  }
  return hash >>> 0;
}

function buildVsaVector(tokens, options = {}) {
  const dim = Number.isInteger(options.dim) && options.dim > 0 ? options.dim : 256;
  const projections = Number.isInteger(options.projections) && options.projections > 0 ? options.projections : 8;
  const vector = new Float32Array(dim);

  for (const token of tokens) {
    const base = hashString(token);
    const step = (hashString(`${token}:step`) % dim) || 1;

    for (let j = 0; j < projections; j += 1) {
      const idx = (base + (j * step)) % dim;
      const sign = (hashString(`${token}:sign:${j}`) & 1) ? 1 : -1;
      vector[idx] += sign;
    }
  }

  let norm = 0;
  for (let i = 0; i < vector.length; i += 1) {
    norm += vector[i] * vector[i];
  }
  norm = Math.sqrt(norm);

  if (norm > 0) {
    for (let i = 0; i < vector.length; i += 1) {
      vector[i] /= norm;
    }
  }

  return vector;
}

function cosineSimilarity(left, right) {
  if (!left || !right || left.length !== right.length) {
    return 0;
  }
  let sum = 0;
  for (let i = 0; i < left.length; i += 1) {
    sum += left[i] * right[i];
  }
  return sum;
}

export class SymbolRegistry {
  constructor(entries = [], options = {}) {
    this._entries = new Map();
    this._snapshotCounter = Number.isInteger(options.snapshotCounter) ? options.snapshotCounter : 0;
    this._sortAliases = new Map();

    for (const entry of entries) {
      this._entries.set(entry.symbol, {
        ...entry,
        semanticHint: typeof entry.semanticHint === 'string' && entry.semanticHint.trim()
          ? entry.semanticHint.trim()
          : null,
        usageCount: Number.isInteger(entry.usageCount) && entry.usageCount >= 0 ? entry.usageCount : 0,
        argSorts: [...(entry.argSorts || [])],
      });
    }

    if (Array.isArray(options.sortAliases)) {
      for (const alias of options.sortAliases) {
        if (!alias || typeof alias.alias !== 'string' || typeof alias.canonicalSort !== 'string') {
          continue;
        }
        this._sortAliases.set(alias.alias.toLowerCase(), alias.canonicalSort);
      }
    }
  }

  clone() {
    return new SymbolRegistry(this.listEntries(), {
      snapshotCounter: this._snapshotCounter,
      sortAliases: this.listSortAliases(),
    });
  }

  listEntries() {
    return [...this._entries.values()]
      .map((entry) => ({
        ...entry,
        argSorts: [...entry.argSorts],
      }))
      .sort((left, right) => left.symbol.localeCompare(right.symbol));
  }

  listSortAliases() {
    return [...this._sortAliases.entries()]
      .map(([alias, canonicalSort]) => ({ alias, canonicalSort }))
      .sort((left, right) => left.alias.localeCompare(right.alias));
  }

  get(symbol) {
    const found = this._entries.get(symbol);
    return found
      ? {
        ...found,
        argSorts: [...found.argSorts],
      }
      : null;
  }

  setSortAliases(canonicalSort, aliases) {
    if (typeof canonicalSort !== 'string' || !canonicalSort.trim()) {
      return;
    }

    if (!Array.isArray(aliases)) {
      return;
    }

    for (const alias of aliases) {
      if (typeof alias !== 'string' || !alias.trim()) {
        continue;
      }
      this._sortAliases.set(alias.toLowerCase(), canonicalSort);
    }
  }

  resolveSort(sortName) {
    if (typeof sortName !== 'string') {
      return sortName;
    }
    return this._sortAliases.get(sortName.toLowerCase()) || sortName;
  }

  mergeDeclarations(declarations, options = {}) {
    const declaredIn = typeof options.declaredIn === 'string' && options.declaredIn.trim()
      ? options.declaredIn
      : 'unknown';

    const accepted = [];
    const conflicts = [];
    const warnings = [];

    for (const declaration of declarations) {
      const nextEntry = canonicalizeDeclaration(declaration, declaredIn);

      if (nextEntry.kind === 'sort' && Array.isArray(declaration.aliases)) {
        this.setSortAliases(nextEntry.symbol, declaration.aliases);
      }

      if (nextEntry.kind === 'sort' && typeof declaration.aliasOf === 'string' && declaration.aliasOf.trim()) {
        this.setSortAliases(declaration.aliasOf, [nextEntry.symbol]);
      }

      const current = this._entries.get(nextEntry.symbol);

      if (!current) {
        warnings.push(...this._detectNearDuplicateWarnings(nextEntry));
        this._entries.set(nextEntry.symbol, nextEntry);
        accepted.push({
          type: 'new',
          symbol: nextEntry.symbol,
          entry: {
            ...nextEntry,
            argSorts: [...nextEntry.argSorts],
          },
        });
        continue;
      }

      if (structuralKey(current, (name) => this.resolveSort(name)) === structuralKey(nextEntry, (name) => this.resolveSort(name))) {
        if (!current.semanticHint && nextEntry.semanticHint) {
          current.semanticHint = nextEntry.semanticHint;
        }
        accepted.push({
          type: 'idempotent',
          symbol: nextEntry.symbol,
          entry: {
            ...current,
            argSorts: [...current.argSorts],
          },
        });
        continue;
      }

      conflicts.push({
        symbol: nextEntry.symbol,
        reason: 'incompatible-signature',
        existing: {
          ...current,
          argSorts: [...current.argSorts],
        },
        incoming: {
          ...nextEntry,
          argSorts: [...nextEntry.argSorts],
        },
      });
    }

    return {
      accepted,
      conflicts,
      warnings,
    };
  }

  incrementUsage(symbol, count = 1) {
    const entry = this._entries.get(symbol);
    if (!entry) {
      return;
    }

    if (!Number.isFinite(count) || count <= 0) {
      return;
    }

    entry.usageCount += count;
  }

  toEncodingContext(options = {}) {
    const strategy = typeof options.strategy === 'string' && options.strategy.trim()
      ? options.strategy.trim()
      : 'usage-topk';
    const maxSymbols = Number.isInteger(options.maxSymbols) && options.maxSymbols > 0
      ? options.maxSymbols
      : null;

    const queryTokens = Array.isArray(options.queryTerms)
      ? options.queryTerms.flatMap((term) => tokenize(term))
      : tokenize(options.queryTerms || '');

    const queryVector = strategy === 'vsa-similarity-topk'
      ? buildVsaVector(queryTokens, {
        dim: options.vectorDim,
        projections: options.vectorProjections,
      })
      : null;

    const scored = this.listEntries().map((entry) => {
      const entryTokens = [
        ...tokenize(entry.symbol),
        ...tokenize(entry.semanticHint || ''),
        ...entry.argSorts.flatMap((sortName) => tokenize(sortName)),
        ...tokenize(entry.resultSort || ''),
      ];

      let score = 0;
      let similarity = null;

      if (strategy === 'vsa-similarity-topk') {
        const entryVector = buildVsaVector(entryTokens, {
          dim: options.vectorDim,
          projections: options.vectorProjections,
        });
        similarity = cosineSimilarity(queryVector, entryVector);
        score = (similarity * 100000) + entry.usageCount;
      } else {
        score = (entry.usageCount * 100) + overlapScore(queryTokens, entryTokens);
      }

      return {
        entry,
        score,
        similarity,
      };
    });

    scored.sort((left, right) => {
      if (left.score !== right.score) {
        return right.score - left.score;
      }
      if (left.entry.usageCount !== right.entry.usageCount) {
        return right.entry.usageCount - left.entry.usageCount;
      }
      return left.entry.symbol.localeCompare(right.entry.symbol);
    });

    const selected = maxSymbols === null
      ? scored.map((row) => row.entry)
      : scored.slice(0, maxSymbols).map((row) => row.entry);

    return {
      strategy,
      reservedPrefixes: ['hp_internal_'],
      rules: [
        'REUSE existing symbols when they match the concept.',
        'DO NOT introduce synonym predicates/functions for existing concepts.',
      ],
      sortAliases: this.listSortAliases(),
      symbols: selected.map((entry) => ({
        symbol: entry.symbol,
        kind: entry.kind,
        arity: entry.arity,
        argSorts: [...entry.argSorts],
        resultSort: entry.resultSort,
        semanticHint: entry.semanticHint,
        usageCount: entry.usageCount,
      })),
    };
  }

  createSnapshot() {
    this._snapshotCounter += 1;
    return {
      snapshotId: `reg_${String(this._snapshotCounter).padStart(4, '0')}`,
      entries: this.listEntries(),
      sortAliases: this.listSortAliases(),
    };
  }

  _detectNearDuplicateWarnings(nextEntry) {
    const warnings = [];

    for (const existing of this._entries.values()) {
      if (existing.symbol === nextEntry.symbol) {
        continue;
      }

      if (nextEntry.kind === 'sort' && existing.kind === 'sort') {
        const nextName = normalizeName(nextEntry.symbol);
        const existingName = normalizeName(existing.symbol);
        const aliasMatches = this.resolveSort(nextEntry.symbol) === existing.symbol
          || this.resolveSort(existing.symbol) === nextEntry.symbol;

        if (aliasMatches || nextName.includes(existingName) || existingName.includes(nextName)) {
          warnings.push({
            type: 'possible-sort-alias',
            symbol: nextEntry.symbol,
            nearSymbol: existing.symbol,
            reason: 'sort-name similarity or alias mapping indicates potential semantic overlap',
          });
        }
        continue;
      }

      if (nextEntry.kind !== existing.kind) {
        continue;
      }

      if (nextEntry.arity !== existing.arity) {
        continue;
      }

      const compatibleArgs = nextEntry.argSorts.every((sortName, index) => {
        return this.resolveSort(sortName) === this.resolveSort(existing.argSorts[index]);
      });
      const compatibleResult = this.resolveSort(nextEntry.resultSort) === this.resolveSort(existing.resultSort);

      if (!compatibleArgs || !compatibleResult) {
        continue;
      }

      warnings.push({
        type: 'possible-semantic-duplicate',
        symbol: nextEntry.symbol,
        nearSymbol: existing.symbol,
        reason: 'same kind/arity/sort signature as an existing symbol',
      });
    }

    return warnings;
  }
}
