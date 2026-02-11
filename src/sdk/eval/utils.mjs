export function uniquePreserveOrder(values) {
  const seen = new Set();
  const out = [];

  for (const value of values) {
    if (seen.has(value)) {
      continue;
    }
    seen.add(value);
    out.push(value);
  }

  return out;
}

export function timestampSlug(now = new Date()) {
  return now.toISOString().replaceAll(':', '-').replaceAll('.', '-');
}
