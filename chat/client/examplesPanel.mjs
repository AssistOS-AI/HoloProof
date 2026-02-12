function safeText(value, fallback = '') {
  if (typeof value !== 'string') {
    return fallback;
  }
  const trimmed = value.trim();
  return trimmed || fallback;
}

function toExampleItems(scenarios = []) {
  const items = [];
  for (const scenario of scenarios) {
    const preview = Array.isArray(scenario.knowledgePreview) ? scenario.knowledgePreview : [];
    for (const problem of scenario.problems || []) {
      items.push({
        scenarioId: scenario.id,
        scenarioTitle: scenario.title,
        category: scenario.category,
        knowledgePreview: preview,
        prompt: safeText(problem.prompt),
        expectedAnswer: safeText(problem.expectedAnswer, 'Expected answer depends on current world strategy.'),
      });
    }
  }
  return items;
}

function createPreviewList(preview) {
  if (!Array.isArray(preview) || preview.length === 0) {
    const fallback = document.createElement('p');
    fallback.className = 'example-line';
    fallback.textContent = 'No knowledge preview available.';
    return fallback;
  }

  const list = document.createElement('ul');
  list.className = 'example-list';
  for (const line of preview) {
    const item = document.createElement('li');
    item.textContent = line;
    list.appendChild(item);
  }
  return list;
}

function createExampleCard(example, index, onRunExample) {
  const card = document.createElement('article');
  card.className = 'example-card';

  card.innerHTML = `
    <div class="cat">${safeText(example.category, 'General')}</div>
    <div class="example-index">Example ${index + 1}</div>
    <h3>${safeText(example.scenarioTitle, 'Scenario')}</h3>
    <div class="example-block">
      <div class="example-label">Question</div>
      <div class="prompt-preview">${safeText(example.prompt)}</div>
    </div>
    <div class="example-block">
      <div class="example-label">Expected</div>
      <div class="example-line">${safeText(example.expectedAnswer)}</div>
    </div>
  `;

  const knowledgeBlock = document.createElement('div');
  knowledgeBlock.className = 'example-block';
  const knowledgeLabel = document.createElement('div');
  knowledgeLabel.className = 'example-label';
  knowledgeLabel.textContent = 'Facts and Rules to Learn';
  knowledgeBlock.appendChild(knowledgeLabel);
  knowledgeBlock.appendChild(createPreviewList(example.knowledgePreview));
  card.appendChild(knowledgeBlock);

  const button = document.createElement('button');
  button.className = 'load-btn';
  button.textContent = 'Load + Ask in Chat';
  button.addEventListener('click', async () => {
    await onRunExample(example);
  });
  card.appendChild(button);

  return card;
}

export function renderExamplesPanel(container, scenarios, onRunExample) {
  container.innerHTML = '';
  const items = toExampleItems(scenarios);

  for (let i = 0; i < items.length; i += 1) {
    container.appendChild(createExampleCard(items[i], i, onRunExample));
  }
}
