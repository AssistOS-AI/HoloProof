const SENSITIVITY_LEVELS = new Set(['public', 'internal', 'confidential', 'restricted']);

export function deepClone(value) {
  return JSON.parse(JSON.stringify(value));
}

export function nowIso(nowFn) {
  return new Date(nowFn()).toISOString();
}

export function ensureRecord(value, message) {
  if (value === null || typeof value !== 'object' || Array.isArray(value)) {
    throw new Error(message);
  }
}

export function normalizeSensitivity(value) {
  if (typeof value !== 'string') {
    return 'internal';
  }
  const normalized = value.toLowerCase();
  return SENSITIVITY_LEVELS.has(normalized) ? normalized : 'internal';
}

export function acceptedAssertionKeys(world, options = {}) {
  const includeRestricted = options.includeRestricted === true;
  const keys = new Set();
  for (const fragment of world.fragments.values()) {
    if (fragment.status !== 'accepted') {
      continue;
    }
    if (!includeRestricted && fragment.restrictedProvenance) {
      continue;
    }
    keys.add(`${fragment.proposalId}:${fragment.assertionId}`);
  }
  return keys;
}
