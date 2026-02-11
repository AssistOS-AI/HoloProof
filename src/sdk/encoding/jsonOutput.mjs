export function extractJsonObjectText(inputText) {
  const text = String(inputText ?? '').trim();
  if (!text) {
    return null;
  }

  const firstBrace = text.indexOf('{');
  const lastBrace = text.lastIndexOf('}');
  if (firstBrace === -1 || lastBrace === -1 || lastBrace <= firstBrace) {
    return null;
  }

  return text.slice(firstBrace, lastBrace + 1);
}

export function parseJsonObject(inputText) {
  const jsonText = extractJsonObjectText(inputText);
  if (!jsonText) {
    return {
      ok: false,
      value: null,
      error: 'No JSON object detected in LLM output.',
    };
  }

  try {
    const parsed = JSON.parse(jsonText);
    if (!parsed || typeof parsed !== 'object' || Array.isArray(parsed)) {
      return {
        ok: false,
        value: null,
        error: 'LLM JSON output must be an object.',
      };
    }
    return {
      ok: true,
      value: parsed,
      error: null,
    };
  } catch (error) {
    return {
      ok: false,
      value: null,
      error: `Invalid JSON output: ${error.message}`,
    };
  }
}
