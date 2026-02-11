import {
  SMT_STRATEGIES,
  INTUITION_STRATEGIES,
  REGISTRY_CONTEXT_DISABLED,
  REGISTRY_CONTEXT_STRATEGIES,
  VSA_REPRESENTATIONS,
  VSA_DISABLED,
} from './constants.mjs';
import { uniquePreserveOrder } from './utils.mjs';

export function buildCombinationId(parts) {
  return [parts.smt.id, parts.intuition.id, parts.vsa.id, parts.registryContext.id, parts.llm.id].join('__');
}

export function firstSmtBySolver(solver, smtStrategies = SMT_STRATEGIES) {
  return smtStrategies.find((strategy) => strategy.solver === solver) || smtStrategies[0];
}

export function vsaRepresentationsFor(intuitionStrategy, mode, options = {}) {
  const vsaRepresentations = options.vsaRepresentations || VSA_REPRESENTATIONS;
  const vsaDisabled = options.vsaDisabled || VSA_DISABLED;

  if (!intuitionStrategy.usesVSARepresentation) {
    return [vsaDisabled];
  }

  if (mode === 'smoke') {
    return [vsaRepresentations[0]];
  }

  return vsaRepresentations;
}

export function buildCombinations(mode, llmProfiles, options = {}) {
  const smtStrategies = options.smtStrategies || SMT_STRATEGIES;
  const intuitionStrategies = options.intuitionStrategies || INTUITION_STRATEGIES;
  const registryContextStrategies = options.registryContextStrategies || REGISTRY_CONTEXT_STRATEGIES;
  const registryContextDisabled = options.registryContextDisabled || REGISTRY_CONTEXT_DISABLED;

  const smtList = mode === 'smoke'
    ? uniquePreserveOrder([firstSmtBySolver('z3', smtStrategies), firstSmtBySolver('cvc5', smtStrategies)])
    : smtStrategies;

  const combinations = [];

  for (const smt of smtList) {
    for (const intuition of intuitionStrategies) {
      const vsaList = vsaRepresentationsFor(intuition, mode, options);
      for (const vsa of vsaList) {
        for (const registryContext of registryContextStrategies.length
          ? registryContextStrategies
          : [registryContextDisabled]) {
          for (const llm of llmProfiles) {
            combinations.push({
              id: buildCombinationId({ smt, intuition, vsa, registryContext, llm }),
              smt,
              intuition,
              vsa,
              registryContext,
              llm,
            });
          }
        }
      }
    }
  }

  return combinations;
}
