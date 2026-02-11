function positiveInt(value, fallback) {
  return Number.isInteger(value) && value > 0 ? value : fallback;
}

export function decideExpansion(context = {}) {
  const round = positiveInt(context.round, 1);
  const maxRounds = positiveInt(context.maxRounds, 3);
  const expansionStep = positiveInt(context.expansionStep, 50);
  const remainingCandidates = positiveInt(context.remainingCandidates, 0);
  const currentVerdict = context.currentVerdict || 'unknown';
  const previousVerdict = context.previousVerdict || null;

  if (currentVerdict !== 'unknown') {
    return {
      action: 'stop',
      reason: 'verdict-resolved',
      nextAddCount: 0,
    };
  }

  if (round >= maxRounds) {
    return {
      action: 'stop',
      reason: 'max-rounds-reached',
      nextAddCount: 0,
    };
  }

  if (remainingCandidates <= 0) {
    return {
      action: 'stop',
      reason: 'no-candidates-left',
      nextAddCount: 0,
    };
  }

  const noProgress = previousVerdict === 'unknown'
    && currentVerdict === 'unknown'
    && Number.isInteger(context.previousActiveCount)
    && Number.isInteger(context.currentActiveCount)
    && context.previousActiveCount === context.currentActiveCount;

  if (noProgress) {
    return {
      action: 'stop',
      reason: 'stagnation-detected',
      nextAddCount: 0,
    };
  }

  return {
    action: 'expand',
    reason: 'retry-with-more-candidates',
    nextAddCount: Math.min(expansionStep, remainingCandidates),
  };
}
