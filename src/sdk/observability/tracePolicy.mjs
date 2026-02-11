function toIso(value) {
  return new Date(value).toISOString();
}

export function deriveTracePolicy(worldPolicy = {}) {
  return {
    sensitivity: worldPolicy.sensitivity || 'internal',
    traceRetentionDays: Number.isInteger(worldPolicy.traceRetentionDays)
      ? worldPolicy.traceRetentionDays
      : 30,
    redactModelValues: worldPolicy.redactModelValues === true,
    allowUnsatCoreDetails: worldPolicy.allowUnsatCoreDetails === true,
  };
}

export function applyTracePolicy(rawTrace, worldPolicy = {}) {
  const policy = deriveTracePolicy(worldPolicy);
  const trace = JSON.parse(JSON.stringify(rawTrace || {}));

  trace.classification = policy.sensitivity;

  const createdAt = trace.createdAt || new Date().toISOString();
  trace.createdAt = toIso(createdAt);

  const ttlMs = Math.max(0, policy.traceRetentionDays) * 24 * 60 * 60 * 1000;
  trace.expiresAt = toIso(Date.parse(trace.createdAt) + ttlMs);

  if (policy.redactModelValues && trace.solverArtifacts?.model) {
    trace.solverArtifacts.model = {
      redacted: true,
      reason: 'world trace policy redacts model values',
    };
  }

  if (!policy.allowUnsatCoreDetails && trace.solverArtifacts?.unsatCore) {
    const unsatCore = trace.solverArtifacts.unsatCore;
    trace.solverArtifacts.unsatCore = {
      redacted: true,
      size: Array.isArray(unsatCore) ? unsatCore.length : 0,
    };
  }

  return trace;
}
