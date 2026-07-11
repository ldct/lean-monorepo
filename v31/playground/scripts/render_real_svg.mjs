// Render scripts/real_hierarchy.dot to site/real_hierarchy.svg with the
// graphviz WASM build (local `dot` is not installed), then post-process node
// groups to carry the attribute contract the page JS binds to:
//   <g class="node" data-class-name="X" tabindex="0" role="img" aria-label="X">
// Legend chips (L1.., LFRONTIER, LMIXIN) get no data attributes.
//
// Setup:  npm i @viz-js/viz   (anywhere; point NODE_PATH at its node_modules)
// Run:    NODE_PATH=<dir>/node_modules node scripts/render_real_svg.mjs
import { createRequire } from 'module';
import { readFileSync, writeFileSync } from 'fs';
import { dirname, join } from 'path';
import { fileURLToPath } from 'url';

const require = createRequire(import.meta.url);
const { instance } = require('@viz-js/viz');

const here = dirname(fileURLToPath(import.meta.url));
const dot = readFileSync(join(here, 'real_hierarchy.dot'), 'utf8');

const viz = await instance();
let svg = viz.renderString(dot, { format: 'svg' });

// strip the XML prolog/doctype so the SVG can be inlined in HTML
svg = svg.replace(/^[\s\S]*?(?=<svg)/, '');

// decode the entities graphviz uses in <title> text (node names are plain)
function decode(s) {
  return s
    .replace(/&#(\d+);/g, (_, d) => String.fromCodePoint(Number(d)))
    .replace(/&lt;/g, '<').replace(/&gt;/g, '>').replace(/&quot;/g, '"')
    .replace(/&amp;/g, '&');
}
function escAttr(s) {
  return s.replace(/&/g, '&amp;').replace(/"/g, '&quot;').replace(/</g, '&lt;');
}

let nodeCount = 0;
svg = svg.replace(
  /(<g id="[^"]*" class="node")(>\s*<title>)([^<]*)(<\/title>)/g,
  (m, open, mid, title, close) => {
    const name = decode(title);
    if (/^L\d+$/.test(name) || name === 'LFRONTIER' || name === 'LMIXIN') return m;
    nodeCount++;
    const a = escAttr(name);
    return `${open} data-class-name="${a}" tabindex="0" role="img" aria-label="${a}"${mid}${title}${close}`;
  });

writeFileSync(join(here, '..', 'site', 'real_hierarchy.svg'), svg);
console.log(`wrote site/real_hierarchy.svg (${nodeCount} data-class-name nodes, ${svg.length} bytes)`);
