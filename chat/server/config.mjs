import path from 'node:path';
import { fileURLToPath } from 'node:url';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);

export const PROJECT_ROOT = path.resolve(__dirname, '../..');
export const CHAT_DIR = path.resolve(PROJECT_ROOT, 'chat');
export const SAVE_DIR = path.resolve(PROJECT_ROOT, 'data/chat-sessions');

export const HOST = process.env.HOLOPROOF_CHAT_HOST || '127.0.0.1';
export const PORT = Number(process.env.HOLOPROOF_CHAT_PORT || 8787);

export const STRATEGY_OPTIONS = {
  smtStrategy: [
    { id: 'smt-z3-incremental-refutation', label: 'Z3 - Incremental Refutation' },
    { id: 'smt-z3-incremental-model', label: 'Z3 - Model Finding' },
    { id: 'smt-cvc5-incremental-refutation', label: 'CVC5 - Incremental Refutation' },
    { id: 'smt-cvc5-incremental-model', label: 'CVC5 - Model Finding' },
  ],
  intuitionStrategy: [
    { id: 'no-intuition', label: 'No Intuition' },
    { id: 'vsa-intuition', label: 'VSA Intuition' },
  ],
  vsaRepresentation: [
    { id: 'vsa-disabled', label: 'Disabled' },
    { id: 'vsa-hrr-cosine-topk', label: 'HRR Cosine Top-K' },
    { id: 'vsa-hdc-binary-hamming-topk', label: 'HDC Binary Hamming Top-K' },
  ],
  llmProfile: [
    { id: 'llm-fast-default', label: 'LLM Fast' },
    { id: 'llm-deep-default', label: 'LLM Deep' },
  ],
  registryContextStrategy: [
    { id: 'usage-topk', label: 'Usage Top-K' },
    { id: 'vsa-similarity-topk', label: 'VSA Similarity Top-K' },
  ],
};

export const CONTENT_TYPES = {
  '.html': 'text/html; charset=utf-8',
  '.css': 'text/css; charset=utf-8',
  '.js': 'application/javascript; charset=utf-8',
  '.mjs': 'application/javascript; charset=utf-8',
  '.json': 'application/json; charset=utf-8',
  '.svg': 'image/svg+xml',
  '.png': 'image/png',
  '.jpg': 'image/jpeg',
  '.jpeg': 'image/jpeg',
  '.ico': 'image/x-icon',
};
