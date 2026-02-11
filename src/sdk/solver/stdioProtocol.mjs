export function buildSyncSentinel(sequenceId) {
  return `HP_SYNC_${String(sequenceId).padStart(6, '0')}`;
}

export function appendSyncProbe(commandText, sequenceId) {
  const sentinel = buildSyncSentinel(sequenceId);
  const normalized = String(commandText || '').trimEnd();
  return `${normalized}\n(echo "${sentinel}")\n`;
}

export function extractResponseUntilSentinel(bufferText, sentinel) {
  const marker = `${sentinel}`;
  const index = bufferText.indexOf(marker);

  if (index === -1) {
    return {
      complete: false,
      responseText: null,
      remaining: bufferText,
    };
  }

  const afterMarkerStart = index + marker.length;
  const newlineIndex = bufferText.indexOf('\n', afterMarkerStart);
  const cutAt = newlineIndex === -1 ? bufferText.length : newlineIndex + 1;

  return {
    complete: true,
    responseText: bufferText.slice(0, index).trim(),
    remaining: bufferText.slice(cutAt),
  };
}

export function parseCheckSatResponse(responseText) {
  const lines = String(responseText || '')
    .split('\n')
    .map((line) => line.trim())
    .filter(Boolean);

  for (const line of lines) {
    if (line === 'sat' || line === 'unsat' || line === 'unknown') {
      return line;
    }
  }

  return null;
}

export function parseSExpressionBlock(responseText) {
  const text = String(responseText || '').trim();
  if (!text) {
    return null;
  }

  let depth = 0;
  let started = false;

  for (let i = 0; i < text.length; i += 1) {
    const ch = text[i];

    if (ch === '(') {
      depth += 1;
      started = true;
    } else if (ch === ')') {
      depth -= 1;
      if (depth < 0) {
        return null;
      }
    }
  }

  if (!started || depth !== 0) {
    return null;
  }

  return text;
}
