import { promises as fs } from 'node:fs';
import { SMOKE_CASE_IDS } from './constants.mjs';
import { uniquePreserveOrder } from './utils.mjs';

export function extractCaseIdsFromMarkdown(markdownText) {
  const matches = [...markdownText.matchAll(/\bEV\d{3}\b/g)].map((match) => match[0]);

  return uniquePreserveOrder(matches)
    .sort((left, right) => Number(left.slice(2)) - Number(right.slice(2)));
}

export async function loadCaseIdsFromPlan(planPath, options = {}) {
  const readText = options.readText || (async (filePath) => fs.readFile(filePath, 'utf8'));
  const text = await readText(planPath);

  const caseIds = extractCaseIdsFromMarkdown(text);
  if (caseIds.length === 0) {
    throw new Error(`No EVxxx case IDs found in plan file: ${planPath}`);
  }

  return caseIds;
}

export function selectSmokeCases(allCaseIds, options = {}) {
  const smokeCaseIds = options.smokeCaseIds || SMOKE_CASE_IDS;
  const available = new Set(allCaseIds);
  const stratified = smokeCaseIds.filter((caseId) => available.has(caseId));

  if (stratified.length > 0) {
    return stratified;
  }

  const fallbackSize = Number.isInteger(options.fallbackSize) && options.fallbackSize > 0
    ? options.fallbackSize
    : 20;

  return allCaseIds.slice(0, Math.min(fallbackSize, allCaseIds.length));
}
