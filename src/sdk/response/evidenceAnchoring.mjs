function normalizeAnchor(anchor) {
  if (!anchor || typeof anchor !== 'object') {
    return null;
  }

  if (typeof anchor.type !== 'string' || typeof anchor.id !== 'string') {
    return null;
  }

  return `${anchor.type}:${anchor.id}`;
}

export function buildEvidenceAnchorSet(evidence) {
  const anchors = new Set();

  for (const fragmentId of evidence.fragmentIds || []) {
    anchors.add(`fragment:${fragmentId}`);
  }

  for (const modelKey of evidence.modelKeys || []) {
    anchors.add(`model:${modelKey}`);
  }

  for (const coreId of evidence.unsatCoreIds || []) {
    anchors.add(`core:${coreId}`);
  }

  if (typeof evidence.verdict === 'string') {
    anchors.add(`verdict:${evidence.verdict}`);
  }

  return anchors;
}

export function validateAnchoredExplanation(explanation, evidence, options = {}) {
  if (!explanation || typeof explanation !== 'object' || !Array.isArray(explanation.claims)) {
    return {
      valid: false,
      errors: ['Explanation must be an object with claims[] array.'],
      acceptedClaims: [],
      rejectedClaims: [],
    };
  }

  const strict = options.strict !== false;
  const anchorSet = buildEvidenceAnchorSet(evidence || {});
  const acceptedClaims = [];
  const rejectedClaims = [];

  for (let i = 0; i < explanation.claims.length; i += 1) {
    const claim = explanation.claims[i];

    if (!claim || typeof claim !== 'object' || typeof claim.text !== 'string') {
      rejectedClaims.push({ index: i, reason: 'claim must be object with text field' });
      continue;
    }

    if (!Array.isArray(claim.anchors) || claim.anchors.length === 0) {
      rejectedClaims.push({ index: i, reason: 'claim has no anchors' });
      continue;
    }

    const normalized = claim.anchors.map(normalizeAnchor).filter(Boolean);
    if (normalized.length === 0) {
      rejectedClaims.push({ index: i, reason: 'claim anchors are malformed' });
      continue;
    }

    const allKnown = normalized.every((anchor) => anchorSet.has(anchor));
    if (!allKnown) {
      rejectedClaims.push({ index: i, reason: 'claim anchors reference unknown evidence' });
      continue;
    }

    acceptedClaims.push({
      text: claim.text,
      anchors: normalized,
    });
  }

  const errors = rejectedClaims.map((item) => `claims[${item.index}] ${item.reason}`);
  return {
    valid: strict ? rejectedClaims.length === 0 : acceptedClaims.length > 0,
    errors,
    acceptedClaims,
    rejectedClaims,
  };
}

export function buildVerdictNarrationPrefix(verdict) {
  switch (verdict) {
    case 'sat':
      return 'I checked the formal model:';
    case 'unsat':
      return 'I checked the formal proof obligations:';
    case 'unknown':
      return 'I ran formal reasoning, but the result is still inconclusive:';
    default:
      return 'Here is what the formal reasoning shows:';
  }
}
