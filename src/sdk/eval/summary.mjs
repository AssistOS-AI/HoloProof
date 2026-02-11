import { STATUS_VALUES } from './constants.mjs';

export function summarizeByCombination(records, combinations) {
  const map = new Map();

  for (const combo of combinations) {
    map.set(combo.id, {
      combinationId: combo.id,
      strategy: combo,
      totalCases: 0,
      executedCases: 0,
      pass: 0,
      fail: 0,
      unknown: 0,
      error: 0,
      skipped: 0,
      totalElapsedMs: 0,
      avgElapsedMs: null,
      successRate: null,
      speedRatioVsFastest: null,
    });
  }

  for (const record of records) {
    const row = map.get(record.combinationId);
    if (!row) {
      continue;
    }

    row.totalCases += 1;
    row.totalElapsedMs += record.elapsedMs;

    const status = STATUS_VALUES.has(record.status) ? record.status : 'error';
    row[status] += 1;

    if (status !== 'skipped') {
      row.executedCases += 1;
    }
  }

  for (const row of map.values()) {
    if (row.executedCases > 0) {
      row.avgElapsedMs = row.totalElapsedMs / row.executedCases;
      row.successRate = row.pass / row.executedCases;
    }
  }

  const fastestAvg = [...map.values()]
    .filter((row) => Number.isFinite(row.avgElapsedMs) && row.avgElapsedMs > 0)
    .reduce((best, row) => Math.min(best, row.avgElapsedMs), Number.POSITIVE_INFINITY);

  if (Number.isFinite(fastestAvg)) {
    for (const row of map.values()) {
      if (Number.isFinite(row.avgElapsedMs) && row.avgElapsedMs > 0) {
        row.speedRatioVsFastest = row.avgElapsedMs / fastestAvg;
      }
    }
  }

  return [...map.values()];
}

export function summarizeGlobal(records) {
  const global = {
    total: records.length,
    pass: 0,
    fail: 0,
    unknown: 0,
    error: 0,
    skipped: 0,
    totalElapsedMs: 0,
  };

  for (const record of records) {
    const status = STATUS_VALUES.has(record.status) ? record.status : 'error';
    global[status] += 1;
    global.totalElapsedMs += record.elapsedMs;
  }

  const executed = global.total - global.skipped;
  global.executed = executed;
  global.successRate = executed > 0 ? global.pass / executed : null;

  return global;
}

export function csvEscape(value) {
  if (value === null || value === undefined) {
    return '';
  }
  const text = String(value);
  if (/[",\n]/.test(text)) {
    return `"${text.replaceAll('"', '""')}"`;
  }
  return text;
}

export function buildSummaryCsv(summaryRows) {
  const headers = [
    'combinationId',
    'solver',
    'smtStrategy',
    'intuitionStrategy',
    'vsaRepresentation',
    'registryContextStrategy',
    'llmProfile',
    'llmMode',
    'llmModel',
    'totalCases',
    'executedCases',
    'pass',
    'fail',
    'unknown',
    'error',
    'skipped',
    'totalElapsedMs',
    'avgElapsedMs',
    'successRate',
    'speedRatioVsFastest',
  ];

  const lines = [headers.join(',')];

  for (const row of summaryRows) {
    const values = [
      row.combinationId,
      row.strategy.smt.solver,
      row.strategy.smt.id,
      row.strategy.intuition.id,
      row.strategy.vsa.id,
      row.strategy.registryContext.id,
      row.strategy.llm.id,
      row.strategy.llm.mode,
      row.strategy.llm.model,
      row.totalCases,
      row.executedCases,
      row.pass,
      row.fail,
      row.unknown,
      row.error,
      row.skipped,
      row.totalElapsedMs.toFixed(3),
      row.avgElapsedMs !== null ? row.avgElapsedMs.toFixed(3) : '',
      row.successRate !== null ? row.successRate.toFixed(4) : '',
      row.speedRatioVsFastest !== null ? row.speedRatioVsFastest.toFixed(4) : '',
    ].map(csvEscape);

    lines.push(values.join(','));
  }

  return `${lines.join('\n')}\n`;
}
