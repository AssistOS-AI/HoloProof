export function createMessagePanel(options = {}) {
  const chatBox = options.chatBox;
  const llmStatus = options.llmStatus || null;
  const clientLog = typeof options.clientLog === 'function' ? options.clientLog : () => {};
  const onFeedback = typeof options.onFeedback === 'function'
    ? options.onFeedback
    : async () => {};

  let modalBound = false;
  let pendingNode = null;

  function setLlmStatus(kind = 'ready', message = null) {
    if (!llmStatus) {
      return;
    }
    llmStatus.classList.toggle('error', kind === 'error');
    if (message) {
      llmStatus.textContent = message;
      return;
    }
    llmStatus.textContent = kind === 'error' ? 'LLM: error' : 'LLM: ready';
  }

  function llmModeLabel(profile = '') {
    return String(profile || '').toLowerCase().includes('deep') ? 'deep' : 'fast';
  }

  function addSystemMessage(text, options = {}) {
    const node = document.createElement('div');
    node.className = 'msg system';
    if (typeof options.kind === 'string' && options.kind.trim()) {
      node.classList.add(`kind-${options.kind.trim()}`);
    }
    if (options.flash === true) {
      node.classList.add('flash');
    }
    node.textContent = text;
    chatBox.appendChild(node);
    chatBox.scrollTop = chatBox.scrollHeight;
  }

  function addUserMessage(text) {
    const node = document.createElement('div');
    node.className = 'msg user';

    const label = document.createElement('div');
    label.className = 'msg-label';
    label.textContent = 'You';
    node.appendChild(label);

    const body = document.createElement('div');
    body.className = 'msg-body';
    body.textContent = text;
    node.appendChild(body);

    chatBox.appendChild(node);
    chatBox.scrollTop = chatBox.scrollHeight;
  }

  function ensureTechModalBound() {
    if (modalBound) {
      return;
    }

    const modal = document.querySelector('#techModal');
    const closeButtons = [
      document.querySelector('#techModalClose'),
      document.querySelector('#techModalDismiss'),
    ].filter(Boolean);

    for (const button of closeButtons) {
      button.addEventListener('click', () => {
        modal.classList.remove('open');
        modal.setAttribute('aria-hidden', 'true');
      });
    }

    modal.addEventListener('click', (event) => {
      if (event.target === modal) {
        modal.classList.remove('open');
        modal.setAttribute('aria-hidden', 'true');
      }
    });

    modalBound = true;
  }

  function openTechnicalModal(payload) {
    ensureTechModalBound();
    const modal = document.querySelector('#techModal');
    const pre = document.querySelector('#techModalPre');

    const details = {
      turnId: payload.turnId || null,
      type: payload.type || 'query-result',
      solverVerdict: payload.solverVerdict || 'unknown',
      queryVerdict: payload.queryVerdict || 'unknown',
      action: payload.action || null,
      reason: payload.reason || null,
      errors: payload.errors || [],
      surfacedIssues: payload.surfacedIssues || [],
      followupQuestions: payload.followupQuestions || [],
      evidenceAnchors: payload.evidenceAnchors || [],
      strategy: payload.strategy || null,
      worldInfo: payload.worldInfo || null,
      reasoningTrace: payload.reasoningTrace || null,
      rawEncoderText: payload.rawEncoderText || null,
      technical: payload.technical || null,
    };

    pre.textContent = JSON.stringify(details, null, 2);
    modal.classList.add('open');
    modal.setAttribute('aria-hidden', 'false');
  }

  async function copyText(text) {
    const content = String(text || '').trim();
    if (!content) {
      addSystemMessage('Nothing to copy for this answer.');
      return;
    }

    try {
      await navigator.clipboard.writeText(content);
      addSystemMessage('Answer copied to clipboard.');
    } catch (error) {
      clientLog('warn', 'Clipboard write failed', {
        message: error.message,
      });
      addSystemMessage('Clipboard copy failed in this browser context.');
    }
  }

  function createAssistantFooter(payload) {
    const footer = document.createElement('div');
    footer.className = 'msg-footer';

    const meta = document.createElement('div');
    meta.className = 'msg-meta';
    meta.textContent = `${payload.solverVerdict || 'unknown'} • ${payload.queryVerdict || 'unknown'}`;
    footer.appendChild(meta);

    const actions = document.createElement('div');
    actions.className = 'msg-actions';

    const copyBtn = document.createElement('button');
    copyBtn.className = 'icon-btn';
    copyBtn.title = 'Copy answer';
    copyBtn.textContent = '⧉';
    copyBtn.addEventListener('click', async () => {
      await copyText(payload.answerText || '');
    });

    const upBtn = document.createElement('button');
    upBtn.className = 'icon-btn vote';
    upBtn.title = 'Thumbs up';
    upBtn.textContent = '👍';
    upBtn.addEventListener('click', async () => {
      await onFeedback(payload.turnId, 'up', upBtn);
    });

    const downBtn = document.createElement('button');
    downBtn.className = 'icon-btn vote';
    downBtn.title = 'Thumbs down';
    downBtn.textContent = '👎';
    downBtn.addEventListener('click', async () => {
      await onFeedback(payload.turnId, 'down', downBtn);
    });

    const detailsBtn = document.createElement('button');
    detailsBtn.className = 'icon-btn';
    detailsBtn.title = 'Technical details';
    detailsBtn.textContent = '⋯';
    detailsBtn.addEventListener('click', () => {
      openTechnicalModal(payload);
    });

    actions.appendChild(copyBtn);
    actions.appendChild(upBtn);
    actions.appendChild(downBtn);
    actions.appendChild(detailsBtn);
    footer.appendChild(actions);

    return footer;
  }

  function removePendingAssistant() {
    if (pendingNode && pendingNode.parentElement) {
      pendingNode.parentElement.removeChild(pendingNode);
    }
    pendingNode = null;
  }

  function addPendingAssistant() {
    removePendingAssistant();

    const node = document.createElement('div');
    node.className = 'msg assistant pending';

    const label = document.createElement('div');
    label.className = 'msg-label';
    label.textContent = 'HoloProof';
    node.appendChild(label);

    const typing = document.createElement('div');
    typing.className = 'typing-indicator';
    typing.innerHTML = '<span></span><span></span><span></span>';
    node.appendChild(typing);

    const hint = document.createElement('div');
    hint.className = 'msg-meta';
    hint.textContent = 'processing formal reasoning...';
    node.appendChild(hint);

    chatBox.appendChild(node);
    chatBox.scrollTop = chatBox.scrollHeight;
    pendingNode = node;
  }

  function addAssistantMessage(payload) {
    removePendingAssistant();

    const node = document.createElement('div');
    node.className = 'msg assistant';
    if (payload.turnId) {
      node.dataset.turnId = payload.turnId;
    }

    const label = document.createElement('div');
    label.className = 'msg-label';
    label.textContent = 'HoloProof';
    node.appendChild(label);

    const body = document.createElement('div');
    body.className = 'msg-body';

    const fallbackError = Array.isArray(payload.errors) && payload.errors.length > 0
      ? payload.errors.join('\n')
      : '(no answer)';

    body.textContent = payload.answerText || fallbackError;
    node.appendChild(body);
    node.appendChild(createAssistantFooter(payload));

    chatBox.appendChild(node);
    chatBox.scrollTop = chatBox.scrollHeight;

    if (payload.type === 'query-error' || payload.type === 'runtime-error' || payload.solverVerdict === 'error') {
      clientLog('error', 'Assistant returned error payload', payload);
      if (String(payload.reason || '').includes('llm')) {
        setLlmStatus('error', 'LLM: error');
        addSystemMessage(
          `LLM error: ${payload.errors?.[0] || payload.answerText || 'unknown error'}`,
          { kind: 'error', flash: true },
        );
      }
      return;
    }

    clientLog('info', 'Assistant payload rendered', {
      turnId: payload.turnId,
      solverVerdict: payload.solverVerdict,
      queryVerdict: payload.queryVerdict,
      action: payload.action,
      reason: payload.reason,
    });
    setLlmStatus('ready', 'LLM: ready');
  }

  function addGuideMessage(guide = {}) {
    const node = document.createElement('div');
    node.className = 'msg assistant guide';

    const label = document.createElement('div');
    label.className = 'msg-label';
    label.textContent = 'HoloProof';
    node.appendChild(label);

    const body = document.createElement('div');
    body.className = 'msg-body';

    const lines = [];
    if (guide.title) {
      lines.push(`Loaded: ${guide.title}`);
    }
    if (guide.loadHint) {
      lines.push(`What was loaded: ${guide.loadHint}`);
    }

    if (Array.isArray(guide.knowledgePreview) && guide.knowledgePreview.length > 0) {
      lines.push('Knowledge snapshot:');
      for (const item of guide.knowledgePreview.slice(0, 4)) {
        lines.push(`- ${item}`);
      }
    }

    if (guide.selectedQuestion) {
      lines.push(`Question to run: ${guide.selectedQuestion}`);
    }
    if (guide.expectedAnswer) {
      lines.push(`Expected answer: ${guide.expectedAnswer}`);
    }

    body.textContent = lines.join('\n');
    node.appendChild(body);

    chatBox.appendChild(node);
    chatBox.scrollTop = chatBox.scrollHeight;
  }

  return {
    setLlmStatus,
    llmModeLabel,
    addSystemMessage,
    addUserMessage,
    addPendingAssistant,
    removePendingAssistant,
    addAssistantMessage,
    addGuideMessage,
  };
}
