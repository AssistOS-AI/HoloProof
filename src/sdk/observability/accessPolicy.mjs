function asSet(values) {
  if (!Array.isArray(values)) {
    return new Set();
  }
  return new Set(values.map((value) => String(value)));
}

export function canAccessTrace(trace = {}, actor = {}) {
  const visibility = trace.accessPolicy?.visibility || 'world-members';

  if (visibility === 'public') {
    return true;
  }

  const actorId = actor.actorId ? String(actor.actorId) : null;
  const actorRoles = asSet(actor.roles || []);
  const allowedActorIds = asSet(trace.accessPolicy?.allowedActorIds || []);
  const allowedRoles = asSet(trace.accessPolicy?.allowedRoles || []);

  if (actorId && allowedActorIds.has(actorId)) {
    return true;
  }

  for (const role of actorRoles) {
    if (allowedRoles.has(role)) {
      return true;
    }
  }

  return false;
}

export function applyTraceAccessPolicy(trace = {}, actor = {}) {
  const allowed = canAccessTrace(trace, actor);
  if (allowed) {
    return {
      allowed: true,
      trace,
    };
  }

  return {
    allowed: false,
    trace: {
      ...trace,
      solverArtifacts: {
        model: { redacted: true, reason: 'access-policy' },
        unsatCore: { redacted: true, reason: 'access-policy' },
      },
      redacted: true,
    },
  };
}
