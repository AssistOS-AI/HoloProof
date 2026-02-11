const CONTROL_CHAR_RE = /[\u0000-\u0008\u000B\u000C\u000E-\u001F\u007F]/g;

export function sanitizePromptText(text, options = {}) {
  const maxLength = Number.isInteger(options.maxLength) && options.maxLength > 0
    ? options.maxLength
    : 12000;

  const normalized = String(text ?? '')
    .replace(CONTROL_CHAR_RE, ' ')
    .replace(/\r\n?/g, '\n')
    .replace(/[ \t]+\n/g, '\n')
    .replace(/\n{3,}/g, '\n\n')
    .trim();

  if (normalized.length <= maxLength) {
    return normalized;
  }

  return normalized.slice(0, maxLength);
}

export function sanitizeMetadata(metadata = {}, options = {}) {
  const out = {};
  for (const [key, value] of Object.entries(metadata || {})) {
    if (value === null || value === undefined) {
      continue;
    }

    if (Array.isArray(value)) {
      out[key] = value
        .slice(0, 50)
        .map((item) => sanitizePromptText(item, options))
        .filter(Boolean);
      continue;
    }

    if (typeof value === 'object') {
      out[key] = sanitizeMetadata(value, options);
      continue;
    }

    out[key] = sanitizePromptText(value, options);
  }
  return out;
}
