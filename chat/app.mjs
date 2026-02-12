/*
 * HoloProof Chat Client
 * - Fresh server session per browser tab load.
 * - SSE stream for turn lifecycle and assistant output.
 * - LLM + solver execution stays server-side.
 */

import { createMessagePanel } from './client/messagePanel.mjs';
import { renderExamplesPanel } from './client/examplesPanel.mjs';

const $ = (selector) => document.querySelector(selector);
const $$ = (selector) => [...document.querySelectorAll(selector)];

const state = {
  sessionId: null,
  eventSource: null,
  strategyOptions: null,
  strategy: null,
  responseStyle: 'neutral',
  scenarios: [],
  loadedScenarioIds: new Set(),
  pendingQuery: false,
  activeTurnId: null,
  requestController: null,
};

const chatBox = $('#chatMessages');
const chatInput = $('#chatInput');
const sendBtn = $('#sendBtn');
const stopBtn = $('#stopBtn');
const worldInfoText = $('#worldInfoText');
const sessionInfo = $('#sessionInfo');
const quickModelSelect = $('#quickModelSelect');
const responseStyleSelect = $('#responseStyleSelect');
const llmStatus = $('#llmStatus');
function clientLog(level, message, meta = null) {
  const stamp = new Date().toISOString();
  const prefix = `[chat-client][${stamp}]`;
  if (level === 'error') {
    console.error(prefix, message, meta || '');
    return;
  }
  if (level === 'warn') {
    console.warn(prefix, message, meta || '');
    return;
  }
  console.log(prefix, message, meta || '');
}
async function apiRequest(path, options = {}) {
  const method = options.method || 'GET';
  const body = options.body !== undefined ? JSON.stringify(options.body) : undefined;
  const requestMeta = {
    method,
    path,
    hasBody: Boolean(body),
    sessionId: state.sessionId,
  };

  clientLog('info', 'API request started', requestMeta);
  const response = await fetch(path, {
    method,
    headers: body ? { 'Content-Type': 'application/json' } : undefined,
    body,
    signal: options.signal,
  });

  let payload = null;
  try {
    payload = await response.json();
  } catch {
    payload = null;
  }

  if (!response.ok) {
    const message = payload?.error || `Request failed (${response.status})`;
    clientLog('error', 'API request failed', {
      ...requestMeta,
      status: response.status,
      payload,
    });
    throw new Error(message);
  }

  clientLog('info', 'API request completed', {
    ...requestMeta,
    status: response.status,
  });
  return payload;
}
async function submitFeedback(turnId, vote, button) {
  if (!turnId || !state.sessionId) {
    panel.addSystemMessage('Cannot save feedback for this turn.');
    return;
  }

  try {
    await apiRequest(`/api/sessions/${encodeURIComponent(state.sessionId)}/feedback`, {
      method: 'POST',
      body: { turnId, vote },
    });

    const parent = button.parentElement;
    parent.querySelectorAll('.icon-btn.vote').forEach((node) => {
      node.classList.remove('active');
    });
    button.classList.add('active');
  } catch (error) {
    clientLog('error', 'Feedback save failed', {
      turnId,
      vote,
      message: error.message,
    });
    panel.addSystemMessage(`Feedback could not be saved: ${error.message}`);
  }
}

const panel = createMessagePanel({
  chatBox,
  llmStatus,
  clientLog,
  onFeedback: submitFeedback,
});
function switchTab(name) {
  $$('.tab-btn').forEach((button) => {
    button.classList.toggle('active', button.dataset.tab === name);
  });
  $$('.tab-panel').forEach((panelNode) => {
    panelNode.classList.toggle('active', panelNode.id === `tab-${name}`);
  });
}
$$('.tab-btn').forEach((button) => {
  button.addEventListener('click', () => switchTab(button.dataset.tab));
});

function updateWorldInfo(worldInfo = null) {
  if (!state.sessionId) {
    sessionInfo.textContent = 'session: -';
    worldInfoText.textContent = 'world: -';
    return;
  }

  sessionInfo.textContent = `session: ${state.sessionId.slice(0, 8)}`;
  if (!worldInfo) {
    worldInfoText.textContent = 'world: -';
    return;
  }

  worldInfoText.textContent = `${worldInfo.worldId} · registry v${worldInfo.registryVersion} · ${worldInfo.fragmentCount} fragments`;
}

function setInputBusy(busy) {
  state.pendingQuery = busy;
  sendBtn.disabled = busy;
  chatInput.disabled = busy;
  stopBtn.disabled = !busy;
  stopBtn.classList.toggle('show', busy);
}

function closeEventSource() {
  if (state.eventSource) {
    state.eventSource.close();
    state.eventSource = null;
  }
}

function connectSessionEvents(sessionId) {
  closeEventSource();
  const source = new EventSource(`/api/sessions/${encodeURIComponent(sessionId)}/events`);
  state.eventSource = source;

  source.addEventListener('session-ready', (event) => {
    const payload = JSON.parse(event.data);
    clientLog('info', 'SSE session-ready', payload);
    state.strategy = payload.strategy || state.strategy;
    updateWorldInfo(payload.worldInfo || null);
  });

  source.addEventListener('turn-started', (event) => {
    const payload = JSON.parse(event.data);
    state.activeTurnId = payload.turnId || state.activeTurnId;
    clientLog('info', 'SSE turn-started', payload);
  });

  source.addEventListener('assistant', (event) => {
    const payload = JSON.parse(event.data);
    clientLog('info', 'SSE assistant event', {
      turnId: payload.turnId,
      type: payload.type,
      solverVerdict: payload.solverVerdict,
      queryVerdict: payload.queryVerdict,
    });

    panel.addAssistantMessage(payload);
    if (payload.worldInfo) {
      updateWorldInfo(payload.worldInfo);
    }

    if (!state.activeTurnId || payload.turnId === state.activeTurnId) {
      state.activeTurnId = null;
      setInputBusy(false);
      state.requestController = null;
    }
  });

  source.addEventListener('turn-cancelled', (event) => {
    const payload = JSON.parse(event.data);
    clientLog('warn', 'SSE turn-cancelled', payload);
    if (!state.activeTurnId || payload.turnId === state.activeTurnId) {
      state.activeTurnId = null;
      setInputBusy(false);
      state.requestController = null;
      panel.removePendingAssistant();
    }
  });

  source.addEventListener('turn-finished', (event) => {
    const payload = JSON.parse(event.data);
    clientLog('info', 'SSE turn-finished', payload);
    if (state.pendingQuery && (!state.activeTurnId || payload.turnId === state.activeTurnId)) {
      state.activeTurnId = null;
      setInputBusy(false);
      state.requestController = null;
      panel.removePendingAssistant();
    }
  });

  source.addEventListener('system', (event) => {
    const payload = JSON.parse(event.data);
    clientLog('info', 'SSE system event', payload);
    if (payload.text) {
      const textLower = String(payload.text || '').toLowerCase();
      if (textLower.includes('loaded scenario') && payload.payload?.scenarioId) {
        return;
      }
      if (textLower.includes('llm error')) {
        panel.addSystemMessage(payload.text, { kind: 'error', flash: true });
        panel.setLlmStatus('error', 'LLM: error');
      } else {
        panel.addSystemMessage(payload.text);
      }
    }
  });

  source.addEventListener('world-updated', (event) => {
    const payload = JSON.parse(event.data);
    clientLog('info', 'SSE world-updated', payload);
    if (payload.worldInfo) {
      updateWorldInfo(payload.worldInfo);
    }
    if (payload.strategy) {
      state.strategy = payload.strategy;
      syncStrategySelectors();
    }
  });

  source.addEventListener('strategy-updated', (event) => {
    const payload = JSON.parse(event.data);
    clientLog('info', 'SSE strategy-updated', payload);
    state.strategy = payload.strategy || state.strategy;
    syncStrategySelectors();
    if (payload.worldInfo) {
      updateWorldInfo(payload.worldInfo);
    }
  });

  source.addEventListener('solver-event', (event) => {
    const payload = JSON.parse(event.data);
    clientLog('warn', 'SSE solver-event', payload);
    if (payload.type === 'session-recovered') {
      panel.addSystemMessage('Solver session recovered and query was rerun from server state.');
    }
  });

  source.onerror = (event) => {
    clientLog('error', 'SSE error', {
      sessionId,
      readyState: source.readyState,
      eventType: event?.type || null,
    });
    panel.addSystemMessage('SSE connection lost. Start a new session if updates stop.');
  };
}

function syncStrategySelectors() {
  if (!state.strategy) {
    return;
  }

  for (const key of ['smtStrategy', 'intuitionStrategy', 'vsaRepresentation', 'llmProfile']) {
    const select = $(`#strategy-${key}`);
    if (!select || !state.strategy[key]) {
      continue;
    }
    select.value = state.strategy[key];
  }

  if (quickModelSelect && state.strategy?.llmProfile) {
    quickModelSelect.value = state.strategy.llmProfile;
    panel.setLlmStatus('ready', `LLM: ${panel.llmModeLabel(state.strategy.llmProfile)}`);
  }
}

function initStrategySelectors() {
  if (!state.strategyOptions) {
    return;
  }

  if (quickModelSelect) {
    const llmOptions = state.strategyOptions.llmProfile || [];
    if (llmOptions.length > 0) {
      quickModelSelect.innerHTML = '';
      for (const option of llmOptions) {
        const node = document.createElement('option');
        node.value = option.id;
        node.textContent = option.label;
        quickModelSelect.appendChild(node);
      }
    }
  }

  const keys = ['smtStrategy', 'intuitionStrategy', 'vsaRepresentation', 'llmProfile'];
  for (const key of keys) {
    const select = $(`#strategy-${key}`);
    if (!select) {
      continue;
    }

    const options = state.strategyOptions[key] || [];
    select.innerHTML = '';
    for (const option of options) {
      const node = document.createElement('option');
      node.value = option.id;
      node.textContent = option.label;
      select.appendChild(node);
    }

    select.onchange = async () => {
      if (!state.sessionId) {
        return;
      }
      try {
        const response = await apiRequest(`/api/sessions/${encodeURIComponent(state.sessionId)}/strategy`, {
          method: 'POST',
          body: { [key]: select.value },
        });
        state.strategy = response.strategy;
        updateWorldInfo(response.worldInfo);
        syncStrategySelectors();
      } catch (error) {
        clientLog('error', 'Strategy update failed', {
          key,
          value: select.value,
          message: error.message,
        });
        panel.addSystemMessage(`Strategy update failed: ${error.message}`);
      }
    };
  }

  syncStrategySelectors();
}

async function refreshSavedSessions() {
  const select = $('#savedSessionSelect');
  if (!select) {
    return;
  }

  try {
    const payload = await apiRequest('/api/saved-sessions');
    select.innerHTML = '';
    const items = payload.saved || [];

    if (items.length === 0) {
      const option = document.createElement('option');
      option.value = '';
      option.textContent = 'No saved snapshots';
      select.appendChild(option);
      return;
    }

    for (const item of items) {
      const option = document.createElement('option');
      option.value = item.savedId;
      option.textContent = `${item.label || item.savedId} (${item.createdAt})`;
      select.appendChild(option);
    }
  } catch (error) {
    clientLog('error', 'Saved session list failed', {
      message: error.message,
    });
    panel.addSystemMessage(`Could not list saved sessions: ${error.message}`);
  }
}

async function startNewSession(savedId = null) {
  const payload = await apiRequest('/api/session', {
    method: 'POST',
    body: savedId ? { savedId } : {},
  });

  state.sessionId = payload.session.sessionId;
  state.strategyOptions = payload.strategyOptions;
  state.strategy = payload.session.strategy;
  state.loadedScenarioIds = new Set();
  state.activeTurnId = null;
  state.requestController = null;
  panel.removePendingAssistant();
  panel.setLlmStatus('ready', 'LLM: ready');

  clientLog('info', 'Session started', {
    sessionId: state.sessionId,
    restoredFrom: payload.restoredFrom || null,
    llmAvailable: payload.session.llmAvailable,
  });

  connectSessionEvents(state.sessionId);
  initStrategySelectors();
  updateWorldInfo(payload.session.worldInfo);

  if (savedId) {
    panel.addSystemMessage(`Started new tab session from snapshot "${savedId}".`);
  } else {
    panel.addSystemMessage('Started new server session. Each tab refresh creates a new session ID.');
  }

  await refreshSavedSessions();
}

async function loadScenario(scenarioId, options = {}) {
  if (!state.sessionId) {
    return { ok: false, message: 'No active session.' };
  }

  const scenarioMeta = state.scenarios.find((scenario) => scenario.id === scenarioId) || null;

  if (!options.force && state.loadedScenarioIds.has(scenarioId)) {
    clientLog('info', 'Scenario already loaded in session, skipping reload', {
      sessionId: state.sessionId,
      scenarioId,
    });
    panel.addSystemMessage('Knowledge pack already loaded in this session.', {
      kind: 'success',
    });
    panel.addGuideMessage({
      title: scenarioMeta?.title || scenarioId,
      knowledgePreview: scenarioMeta?.knowledgePreview || [],
    });
    return { ok: true, skipped: true, payload: null };
  }

  try {
    const payload = await apiRequest(`/api/sessions/${encodeURIComponent(state.sessionId)}/load-scenario`, {
      method: 'POST',
      body: { scenarioId },
    });
    state.loadedScenarioIds.add(scenarioId);
    const allAccepted = payload.acceptedCount === payload.loadedCount;
    panel.addSystemMessage(
      `Loaded "${payload.title}".`,
      { kind: allAccepted ? 'success' : 'warn', flash: true },
    );
    panel.addGuideMessage({
      title: payload.title,
      knowledgePreview: payload.knowledgePreview || scenarioMeta?.knowledgePreview || [],
    });
    updateWorldInfo(payload.worldInfo);
    return { ok: true, payload };
  } catch (error) {
    clientLog('error', 'Scenario load failed', {
      scenarioId,
      message: error.message,
    });
    panel.addSystemMessage(`Scenario load failed: ${error.message}`, {
      kind: 'error',
      flash: true,
    });
    return { ok: false, message: error.message };
  }
}

async function sendQuery(text) {
  if (!state.sessionId) {
    panel.addSystemMessage('No active session.');
    return;
  }
  if (state.pendingQuery) {
    panel.addSystemMessage('Another query is currently running. Stop it or wait for completion.');
    return;
  }

  setInputBusy(true);
  panel.addPendingAssistant();
  panel.setLlmStatus('ready', 'LLM: processing');

  const controller = new AbortController();
  state.requestController = controller;

  try {
    const payload = await apiRequest(`/api/sessions/${encodeURIComponent(state.sessionId)}/message`, {
      method: 'POST',
      body: {
        text,
        responseStyle: state.responseStyle,
      },
      signal: controller.signal,
    });

    state.activeTurnId = payload.turnId || state.activeTurnId;
    clientLog('info', 'Query accepted by server', {
      sessionId: state.sessionId,
      turnId: state.activeTurnId,
      textPreview: String(text || '').slice(0, 160),
    });
  } catch (error) {
    if (error.name === 'AbortError') {
      clientLog('warn', 'Query request aborted on client side', {
        turnId: state.activeTurnId,
      });
      return;
    }

    clientLog('error', 'Query submit failed', {
      sessionId: state.sessionId,
      message: error.message,
    });
    setInputBusy(false);
    state.requestController = null;
    state.activeTurnId = null;
    panel.removePendingAssistant();
    panel.addSystemMessage(`Query failed: ${error.message}`);
    if (String(error.message || '').toLowerCase().includes('llm')) {
      panel.setLlmStatus('error', 'LLM: error');
    }
  }
}

async function cancelCurrentQuery() {
  if (!state.sessionId || !state.pendingQuery) {
    return;
  }

  const turnId = state.activeTurnId;
  if (state.requestController) {
    try {
      state.requestController.abort();
    } catch {
      // Ignore.
    }
  }

  try {
    const payload = await apiRequest(`/api/sessions/${encodeURIComponent(state.sessionId)}/cancel`, {
      method: 'POST',
      body: turnId ? { turnId } : {},
    });

    if (payload.cancelled) {
      panel.addSystemMessage(`Stopped running query ${payload.turnId || ''}`.trim());
    } else if (payload.reason) {
      panel.addSystemMessage(`Stop request ignored: ${payload.reason}`);
    }
  } catch (error) {
    clientLog('error', 'Cancel query failed', {
      turnId,
      message: error.message,
    });
    panel.addSystemMessage(`Could not cancel query: ${error.message}`);
  }
}

function renderExamplesTab() {
  const container = $('#examplesGrid');
  renderExamplesPanel(container, state.scenarios, async (example) => {
    switchTab('chat');
    const loaded = await loadScenario(example.scenarioId);
    if (!loaded.ok) {
      return;
    }

    panel.addUserMessage(example.prompt);
    await sendQuery(example.prompt);
  });
}

async function loadScenarios() {
  const payload = await apiRequest('/api/scenarios');
  state.scenarios = payload.scenarios || [];
  renderExamplesTab();
}

async function handleSend() {
  const text = chatInput.value.trim();
  if (!text || state.pendingQuery) {
    return;
  }

  chatInput.value = '';
  panel.addUserMessage(text);
  await sendQuery(text);
}

sendBtn.addEventListener('click', () => {
  handleSend();
});

chatInput.addEventListener('keydown', (event) => {
  if (event.key === 'Enter' && !event.shiftKey) {
    event.preventDefault();
    handleSend();
  }
});

stopBtn.addEventListener('click', async () => {
  await cancelCurrentQuery();
});

$('#resetBtn').addEventListener('click', async () => {
  chatBox.innerHTML = '';
  await startNewSession();
});

$('#saveSessionBtn').addEventListener('click', async () => {
  if (!state.sessionId) {
    return;
  }

  try {
    const payload = await apiRequest(`/api/sessions/${encodeURIComponent(state.sessionId)}/save`, {
      method: 'POST',
      body: {},
    });
    panel.addSystemMessage(`Saved snapshot "${payload.savedId}".`);
    await refreshSavedSessions();
  } catch (error) {
    panel.addSystemMessage(`Save failed: ${error.message}`);
  }
});

$('#loadSessionBtn').addEventListener('click', async () => {
  const savedId = $('#savedSessionSelect').value;
  if (!savedId) {
    panel.addSystemMessage('Select a saved snapshot first.');
    return;
  }

  chatBox.innerHTML = '';
  await startNewSession(savedId);
});

if (quickModelSelect) {
  quickModelSelect.addEventListener('change', async () => {
    if (!state.sessionId) {
      return;
    }

    try {
      const response = await apiRequest(`/api/sessions/${encodeURIComponent(state.sessionId)}/strategy`, {
        method: 'POST',
        body: { llmProfile: quickModelSelect.value },
      });
      state.strategy = response.strategy;
      syncStrategySelectors();
      panel.addSystemMessage(`LLM profile switched to ${panel.llmModeLabel(quickModelSelect.value)}.`);
    } catch (error) {
      clientLog('error', 'Quick LLM switch failed', {
        value: quickModelSelect.value,
        message: error.message,
      });
      panel.addSystemMessage(`LLM switch failed: ${error.message}`);
      panel.setLlmStatus('error', 'LLM: error');
    }
  });
}

if (responseStyleSelect) {
  responseStyleSelect.value = state.responseStyle;
  responseStyleSelect.addEventListener('change', () => {
    state.responseStyle = responseStyleSelect.value || 'neutral';
    panel.addSystemMessage(`Answer style set to ${state.responseStyle}.`);
  });
}

async function init() {
  try {
    await loadScenarios();
    await startNewSession();
    panel.addSystemMessage('Server session started. Use Examples for end-to-end runs that load knowledge then execute formal reasoning.');
  } catch (error) {
    clientLog('error', 'Initialization failed', {
      message: error.message,
      stack: error.stack,
    });
    panel.addSystemMessage(`Initialization failed: ${error.message}`);
  }
}

init();
