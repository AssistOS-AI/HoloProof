/*
 * HoloProof Chat — Main application module.
 * Handles UI rendering, tab management, and user interaction.
 */
import { ChatOrchestrator, STRATEGY_OPTIONS } from './orchestrator.mjs';
import { DEMO_SCENARIOS } from './demo-scenarios.mjs';

const orchestrator = new ChatOrchestrator();

/* ── DOM refs ── */
const $ = (sel) => document.querySelector(sel);
const $$ = (sel) => [...document.querySelectorAll(sel)];

const chatBox = $('#chatMessages');
const chatInput = $('#chatInput');
const sendBtn = $('#sendBtn');
const worldInfoEl = $('#worldInfo');

/* ── Tab management ── */
function switchTab(name) {
    $$('.tab-btn').forEach(btn => {
        btn.classList.toggle('active', btn.dataset.tab === name);
    });
    $$('.tab-panel').forEach(panel => {
        panel.classList.toggle('active', panel.id === `tab-${name}`);
    });
}

$$('.tab-btn').forEach(btn => {
    btn.addEventListener('click', () => switchTab(btn.dataset.tab));
});

/* ── Strategy selector ── */
function initStrategySelectors() {
    for (const [key, options] of Object.entries(STRATEGY_OPTIONS)) {
        const select = $(`#strategy-${key}`);
        if (!select) continue;
        select.innerHTML = '';
        for (const opt of options) {
            const el = document.createElement('option');
            el.value = opt.id;
            el.textContent = opt.label;
            select.appendChild(el);
        }
        select.addEventListener('change', () => {
            orchestrator.setStrategy(key, select.value);
            updateWorldInfo();
        });
    }
}

/* ── World info display ── */
function updateWorldInfo() {
    const info = orchestrator.getWorldInfo();
    if (!info) {
        worldInfoEl.innerHTML = '<span>No world</span>';
        return;
    }
    worldInfoEl.innerHTML = `
    <span>${info.worldId}</span> ·
    registry v<span>${info.registryVersion}</span> ·
    <span>${info.fragmentCount}</span> fragments ·
    <span>${info.proposalCount}</span> proposals
  `;
}

/* ── Message rendering ── */
function addSystemMessage(text) {
    const msg = document.createElement('div');
    msg.className = 'msg system';
    msg.textContent = text;
    chatBox.appendChild(msg);
    chatBox.scrollTop = chatBox.scrollHeight;
}

function addUserMessage(text) {
    const msg = document.createElement('div');
    msg.className = 'msg user';

    const label = document.createElement('div');
    label.className = 'msg-label';
    label.textContent = 'You';
    msg.appendChild(label);

    const body = document.createElement('div');
    body.className = 'msg-body';
    body.textContent = text;
    msg.appendChild(body);

    chatBox.appendChild(msg);
    chatBox.scrollTop = chatBox.scrollHeight;
}

function addAssistantMessage(response) {
    const msg = document.createElement('div');
    msg.className = 'msg assistant';

    const label = document.createElement('div');
    label.className = 'msg-label';
    label.textContent = 'HoloProof';
    msg.appendChild(label);

    /* Verdict badge */
    const badge = document.createElement('div');
    badge.className = `verdict-badge ${response.reasoning.interpretation || response.reasoning.verdict}`;
    badge.textContent = `${response.reasoning.verdict} — ${response.reasoning.interpretation || ''}`;
    msg.appendChild(badge);

    /* Answer text */
    const answerBody = document.createElement('div');
    answerBody.className = 'msg-body';
    answerBody.textContent = response.answer.text;
    msg.appendChild(answerBody);

    /* Reasoning layers */
    const layers = document.createElement('div');
    layers.className = 'reasoning-layers';

    /* Layer 1: Formalization */
    layers.appendChild(createLayer(
        'formalization',
        'Formalization Intent',
        response.formalization.target + (response.formalization.status === 'simulated' ? '\n\n[simulated — no live LLM encoding]' : ''),
    ));

    /* Layer 2: Reasoning trace */
    layers.appendChild(createLayer(
        'trace',
        'Reasoning Trace',
        response.reasoning.trace,
        true, /* open by default */
    ));

    /* Layer 3: Evidence */
    if (response.evidence && response.evidence.trace) {
        const evidenceText = formatEvidence(response.evidence);
        layers.appendChild(createLayer('evidence', 'Evidence & Trace', evidenceText));
    }

    msg.appendChild(layers);

    /* Strategy chips */
    if (response.strategy) {
        const stratInfo = document.createElement('div');
        stratInfo.className = 'strategy-info';
        for (const [key, value] of Object.entries(response.strategy)) {
            const chip = document.createElement('span');
            chip.className = 'chip';
            chip.textContent = value;
            stratInfo.appendChild(chip);
        }
        msg.appendChild(stratInfo);
    }

    chatBox.appendChild(msg);
    chatBox.scrollTop = chatBox.scrollHeight;
}

function createLayer(className, title, content, openByDefault = false) {
    const layer = document.createElement('div');
    layer.className = `layer ${className}${openByDefault ? ' open' : ''}`;

    const header = document.createElement('div');
    header.className = 'layer-header';
    header.innerHTML = `<span class="dot"></span>${title}<span class="arrow">▶</span>`;
    header.addEventListener('click', () => layer.classList.toggle('open'));
    layer.appendChild(header);

    const body = document.createElement('div');
    body.className = 'layer-content';
    body.textContent = content;
    layer.appendChild(body);

    return layer;
}

function formatEvidence(evidence) {
    const parts = [];
    if (evidence.trace) {
        const t = evidence.trace;
        parts.push(`Classification: ${t.classification || 'N/A'}`);
        if (t.verdict) parts.push(`Verdict: ${t.verdict}`);
        if (t.formalTarget) parts.push(`Target: ${t.formalTarget}`);
        if (t.solverArtifacts?.unsatCore) {
            const core = t.solverArtifacts.unsatCore;
            if (core.redacted) {
                parts.push(`Unsat core: [redacted, ${core.size} items]`);
            } else if (Array.isArray(core)) {
                parts.push(`Unsat core: ${core.join(', ')}`);
            }
        }
        if (t.solverArtifacts?.model) {
            const model = t.solverArtifacts.model;
            if (model.redacted) {
                parts.push(`Model: [redacted]`);
            } else {
                parts.push(`Model keys: ${Object.keys(model).join(', ')}`);
            }
        }
        if (t.expiresAt) parts.push(`Trace expires: ${t.expiresAt}`);
    }
    if (evidence.anchorSet && evidence.anchorSet.length > 0) {
        parts.push(`\nEvidence anchors:\n  ${evidence.anchorSet.join('\n  ')}`);
    }
    return parts.join('\n');
}

/* ── Chat input ── */
function handleSend() {
    const text = chatInput.value.trim();
    if (!text) return;

    addUserMessage(text);
    chatInput.value = '';

    /* Small delay for visual effect */
    setTimeout(() => {
        const response = orchestrator.processQuery(text);
        addAssistantMessage(response);
        updateWorldInfo();
    }, 150);
}

sendBtn.addEventListener('click', handleSend);
chatInput.addEventListener('keydown', (e) => {
    if (e.key === 'Enter' && !e.shiftKey) {
        e.preventDefault();
        handleSend();
    }
});

/* ── Examples tab ── */
function renderExamplesTab() {
    const container = $('#examplesGrid');
    container.innerHTML = '';

    /* Collect all examples from usage-guide format (from scenarios) */
    const allExamples = [];
    for (const scenario of DEMO_SCENARIOS) {
        for (const problem of scenario.problems) {
            allExamples.push({
                category: scenario.category,
                title: scenario.title,
                prompt: problem.prompt,
                formalTarget: problem.formalTarget,
                answer: problem.simulatedResult.answer,
                scenarioId: scenario.id,
            });
        }
    }

    for (const ex of allExamples) {
        const card = document.createElement('article');
        card.className = 'example-card';

        card.innerHTML = `
      <div class="cat">${ex.category}</div>
      <h3>${ex.title}</h3>
      <p>${ex.formalTarget}</p>
      <div class="prompt-preview">${ex.prompt}</div>
    `;

        const loadBtn = document.createElement('button');
        loadBtn.className = 'load-btn';
        loadBtn.textContent = 'Try in Chat →';
        loadBtn.addEventListener('click', () => {
            /* Load scenario knowledge first */
            const loadResult = orchestrator.loadScenarioKnowledge(ex.scenarioId);
            addSystemMessage(`📚 Loaded scenario: ${loadResult.title} — ${loadResult.fragmentCount} fragments, registry v${loadResult.registryVersion}`);
            updateWorldInfo();

            /* Send the prompt */
            addUserMessage(ex.prompt);
            setTimeout(() => {
                const response = orchestrator.processQuery(ex.prompt);
                addAssistantMessage(response);
                updateWorldInfo();
            }, 150);

            switchTab('chat');
        });

        card.appendChild(loadBtn);
        container.appendChild(card);
    }
}

/* ── Knowledge tab ── */
function renderKnowledgeTab() {
    const container = $('#scenarioCards');
    container.innerHTML = '';

    const scenarios = orchestrator.getScenarios();
    for (const scenario of scenarios) {
        const card = document.createElement('article');
        card.className = 'scenario-card';
        card.id = `scenario-${scenario.id}`;

        card.innerHTML = `
      <div class="cat">${scenario.category}</div>
      <h3>${scenario.title}</h3>
      <p>${scenario.description}</p>
      <div class="actions"></div>
    `;

        const actions = card.querySelector('.actions');

        const loadBtn = document.createElement('button');
        loadBtn.className = 'load-kb';
        loadBtn.textContent = '📚 Load Knowledge';
        loadBtn.addEventListener('click', () => {
            const result = orchestrator.loadScenarioKnowledge(scenario.id);
            addSystemMessage(`📚 Loaded "${scenario.title}" — ${result.fragmentCount} fragments, registry v${result.registryVersion}`);
            card.classList.add('loaded');
            updateWorldInfo();
            switchTab('chat');
        });
        actions.appendChild(loadBtn);

        /* Add quick-ask buttons for each problem */
        const detail = orchestrator.getScenarioDetail(scenario.id);
        if (detail) {
            for (let i = 0; i < detail.problems.length; i++) {
                const problem = detail.problems[i];
                const askBtn = document.createElement('button');
                askBtn.className = 'ask-q';
                askBtn.textContent = `🔍 Ask Q${i + 1}`;
                askBtn.title = problem.prompt;
                askBtn.addEventListener('click', () => {
                    /* Ensure knowledge is loaded */
                    const result = orchestrator.loadScenarioKnowledge(scenario.id);
                    addSystemMessage(`📚 Loaded "${scenario.title}" — ${result.fragmentCount} fragments`);
                    card.classList.add('loaded');

                    /* Ask the question */
                    addUserMessage(problem.prompt);
                    setTimeout(() => {
                        const response = orchestrator.processQuery(problem.prompt);
                        addAssistantMessage(response);
                        updateWorldInfo();
                    }, 150);
                    switchTab('chat');
                });
                actions.appendChild(askBtn);
            }
        }

        container.appendChild(card);
    }
}

/* ── Reset ── */
$('#resetBtn').addEventListener('click', () => {
    orchestrator.resetWorld();
    chatBox.innerHTML = '';
    addSystemMessage('🔄 World reset. Load a scenario from the Knowledge tab to start reasoning.');
    updateWorldInfo();
    renderKnowledgeTab(); /* reset loaded states */
});

/* ── Init ── */
initStrategySelectors();
renderExamplesTab();
renderKnowledgeTab();
updateWorldInfo();
addSystemMessage('Welcome to HoloProof Chat. Load a demo scenario from the Knowledge tab, then ask questions to see formal reasoning in action.');
