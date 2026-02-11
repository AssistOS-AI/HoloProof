import { runReasoningQuery } from '../reasoning/queryExecutor.mjs';
import { buildResponseDecisionContext } from '../response/decisionPolicy.mjs';

export async function executeFormalQueryPipeline(options = {}) {
  const reasoning = await runReasoningQuery({
    solverAdapter: options.solverAdapter,
    sessionId: options.sessionId,
    queryPlan: options.queryPlan,
    fragments: options.fragments || [],
    rankedFragmentIds: options.rankedFragmentIds || null,
    intuition: options.intuition || null,
    registryEntries: options.registryEntries || [],
    budget: options.budget || {},
  });

  const response = buildResponseDecisionContext({
    solverOutcome: {
      verdict: reasoning.solverVerdict,
      timeout: reasoning.timeout,
    },
    knowledgeGaps: reasoning.knowledgeGaps,
    policy: options.decoderPolicy || {},
    llmAvailable: options.llmAvailable === true,
  });

  return {
    reasoning,
    response,
  };
}
