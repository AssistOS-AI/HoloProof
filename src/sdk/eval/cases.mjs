import { promises as fs } from 'node:fs';
import path from 'node:path';
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

export async function loadStructuredCaseDefinitions(casesDir, options = {}) {
  const readDir = options.readDir || (async (dirPath) => fs.readdir(dirPath));
  const readText = options.readText || (async (filePath) => fs.readFile(filePath, 'utf8'));
  const entries = await readDir(casesDir);

  const files = entries
    .filter((name) => name.toLowerCase().endsWith('.json'))
    .sort((left, right) => left.localeCompare(right));

  const definitions = [];
  for (const fileName of files) {
    const fullPath = path.join(casesDir, fileName);
    const raw = await readText(fullPath);
    const parsed = JSON.parse(raw);
    if (!parsed || typeof parsed !== 'object') {
      throw new Error(`Invalid structured case file: ${fullPath}`);
    }
    if (typeof parsed.caseId !== 'string' || !/^EV\d{3}$/.test(parsed.caseId)) {
      throw new Error(`Structured case file missing valid caseId: ${fullPath}`);
    }
    definitions.push(parsed);
  }

  return definitions.sort((left, right) => Number(left.caseId.slice(2)) - Number(right.caseId.slice(2)));
}

export async function loadCaseIdsFromStructuredCases(casesDir, options = {}) {
  const definitions = await loadStructuredCaseDefinitions(casesDir, options);
  return definitions.map((item) => item.caseId);
}

export async function loadCaseIdsWithFallback({ casesDir, planPath }, options = {}) {
  const pathExists = options.pathExists || (async (target) => {
    try {
      await fs.access(target);
      return true;
    } catch {
      return false;
    }
  });

  const planCaseIds = await loadCaseIdsFromPlan(planPath, options);

  if (casesDir && await pathExists(casesDir)) {
    const structuredIds = await loadCaseIdsFromStructuredCases(casesDir, options);
    if (structuredIds.length > 0) {
      const planSet = new Set(planCaseIds);
      const merged = planCaseIds.slice();
      for (const caseId of structuredIds) {
        if (!planSet.has(caseId)) {
          merged.push(caseId);
        }
      }
      return {
        source: 'structured-plus-plan',
        caseIds: merged,
      };
    }
  }

  const caseIds = planCaseIds;
  return {
    source: 'plan-markdown',
    caseIds,
  };
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
