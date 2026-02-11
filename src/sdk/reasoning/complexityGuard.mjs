function walkExpr(expr, visitor) {
  if (!expr || typeof expr !== 'object') {
    return;
  }

  visitor(expr);

  if (Array.isArray(expr.args)) {
    for (const arg of expr.args) {
      walkExpr(arg, visitor);
    }
  }

  if (expr.arg && typeof expr.arg === 'object') {
    walkExpr(expr.arg, visitor);
  }

  if (expr.body && typeof expr.body === 'object') {
    walkExpr(expr.body, visitor);
  }
}

function exprMetrics(expr) {
  let nodeCount = 0;
  let quantifierCount = 0;
  let maxDepth = 0;

  function visit(node, depth) {
    if (!node || typeof node !== 'object') {
      return;
    }
    nodeCount += 1;
    if (node.op === 'forall' || node.op === 'exists') {
      quantifierCount += 1;
    }
    if (depth > maxDepth) {
      maxDepth = depth;
    }

    if (Array.isArray(node.args)) {
      for (const arg of node.args) {
        visit(arg, depth + 1);
      }
    }
    if (node.arg && typeof node.arg === 'object') {
      visit(node.arg, depth + 1);
    }
    if (node.body && typeof node.body === 'object') {
      visit(node.body, depth + 1);
    }
  }

  visit(expr, 1);
  return { nodeCount, quantifierCount, maxDepth };
}

function limit(value, fallback) {
  return Number.isInteger(value) && value > 0 ? value : fallback;
}

export function evaluateReasoningComplexity(input = {}) {
  const fragments = Array.isArray(input.fragments) ? input.fragments : [];
  const goal = input.queryPlan?.goal || null;

  let fragmentNodes = 0;
  let fragmentQuantifiers = 0;
  let fragmentDepth = 0;

  for (const fragment of fragments) {
    const metrics = exprMetrics(fragment.expr || {});
    fragmentNodes += metrics.nodeCount;
    fragmentQuantifiers += metrics.quantifierCount;
    fragmentDepth = Math.max(fragmentDepth, metrics.maxDepth);
  }

  const goalMetrics = goal ? exprMetrics(goal) : { nodeCount: 0, quantifierCount: 0, maxDepth: 0 };

  return {
    fragmentCount: fragments.length,
    fragmentNodes,
    fragmentQuantifiers,
    fragmentDepth,
    goalNodes: goalMetrics.nodeCount,
    goalQuantifiers: goalMetrics.quantifierCount,
    goalDepth: goalMetrics.maxDepth,
    totalNodes: fragmentNodes + goalMetrics.nodeCount,
    totalQuantifiers: fragmentQuantifiers + goalMetrics.quantifierCount,
    maxDepth: Math.max(fragmentDepth, goalMetrics.maxDepth),
  };
}

export function checkComplexityBudget(metrics, budget = {}) {
  const maxTotalNodes = limit(budget.maxTotalNodes, 5000);
  const maxQuantifiers = limit(budget.maxQuantifiers, 200);
  const maxDepth = limit(budget.maxExprDepth, 60);

  const violations = [];
  if (metrics.totalNodes > maxTotalNodes) {
    violations.push(`totalNodes ${metrics.totalNodes} exceeds ${maxTotalNodes}`);
  }
  if (metrics.totalQuantifiers > maxQuantifiers) {
    violations.push(`totalQuantifiers ${metrics.totalQuantifiers} exceeds ${maxQuantifiers}`);
  }
  if (metrics.maxDepth > maxDepth) {
    violations.push(`maxDepth ${metrics.maxDepth} exceeds ${maxDepth}`);
  }

  return {
    ok: violations.length === 0,
    violations,
    limits: {
      maxTotalNodes,
      maxQuantifiers,
      maxDepth,
    },
  };
}
