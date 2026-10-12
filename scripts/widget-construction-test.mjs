// Pure rendering and async-state checks against the actual widget module.
import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import vm from 'node:vm';
const context = vm.createContext({ console });
const source = await fs.readFile('widget/construction.js', 'utf8');
const module = new vm.SourceTextModule(source, { context });
await module.link(async name => {
  const values = name === 'react' ? { createElement: () => {} } :
    { useRpcSession: () => {}, EditorContext: {}, mapRpcError: e => e };
  return new vm.SyntheticModule(Object.keys(values), function () {
    for (const [key, value] of Object.entries(values)) this.setExport(key, value);
  }, { context });
});
await module.evaluate();
const { clipLine, precisionFor, needsRefinement, newGeneration, isCurrent } = module.namespace;
const plain = x => JSON.parse(JSON.stringify(x));
assert.deepEqual(plain(clipLine(1, 0, 1, [-2, 2, -2, 2])), [[1, -2], [1, 2]]);
assert.deepEqual(plain(clipLine(0, 1, 0, [-2, 2, -2, 2])), [[-2, 0], [2, 0]]);
assert.equal(clipLine(0, 0, 0, [-2, 2, -2, 2]), null);
assert.equal(clipLine(1, 0, 5, [-2, 2, -2, 2]), null);
assert.ok(precisionFor(1e-10) > precisionFor(4));
assert.equal(precisionFor(1e-200, 480), 512);
assert.ok(needsRefinement({ values: [{ value: '1.4', error: '0.1' }] }, { width: 4 }));
assert.ok(!needsRefinement({ values: [{ value: '1.4', error: '1e-30' }] }, { width: 4 }));
const ref = { current: 0 };
const preview = newGeneration(ref), undo = newGeneration(ref);
assert.ok(!isCurrent(ref, preview));
assert.ok(isCurrent(ref, undo));
console.log('PASS: implicit-line clipping, vertical lines, precision, and stale-reply rejection');

// Render the actual component with a small deterministic React/editor adapter.
// This tests event wiring, not browser layout or the Lean RPC implementation.
let slots = [], cursor = 0, effects = [], tree, requests = [], edits = [];
let rpc, editor;
const react = {
  createElement: (tag, props, ...children) => ({ tag, props: props ?? {}, children: children.flat(Infinity) }),
  useContext: () => editor,
  useState(initial) {
    const i = cursor++;
    if (!(i in slots)) slots[i] = typeof initial === 'function' ? initial() : initial;
    return [slots[i], value => { slots[i] = typeof value === 'function' ? value(slots[i]) : value; }];
  },
  useRef(initial) { const i = cursor++; return slots[i] ??= { current: initial }; },
  useEffect(fn, deps) {
    const i = cursor++, old = slots[i];
    if (!old || deps.some((value, j) => !Object.is(value, old.deps[j]))) {
      slots[i] = { deps };
      effects.push(() => { old?.cleanup?.(); slots[i].cleanup = fn(); });
    }
  },
};
const uiModule = new vm.SourceTextModule(source, { context });
await uiModule.link(async name => {
  const values = name === 'react' ? react :
    { useRpcSession: () => rpc, EditorContext: 'editor', mapRpcError: error => ({ message: error.message }) };
  return new vm.SyntheticModule(Object.keys(values), function () {
    for (const [key, value] of Object.entries(values)) this.setExport(key, value);
  }, { context });
});
await uiModule.evaluate();
const approximation = value => ({ value: String(value), error: '0' });
const point = (index, x, y) => ({ index, kind: 'point', values: [x, y].map(approximation) });
const line = (index, a, b, c) => ({ index, kind: 'line', values: [a, b, c].map(approximation) });
const start = { session: { p: 'initial' }, view: { objects: [point(0, 0, 0), point(1, 1, 0)], choices: [], steps: 0 } };
rpc = { call(name, params) {
  assert.equal(name, 'LeanOrigami.Widget.interact');
  return new Promise((resolve, reject) => requests.push({ params, resolve, reject }));
} };
let version = 7;
editor = { api: { async applyEdit(edit) {
  if (edit.documentChanges[0].textDocument.version !== version) throw new Error('stale document');
  edits.push(edit); version++;
} } };
function render() {
  cursor = 0;
  tree = uiModule.namespace.default({ gate: { p: 'goal' }, target: '1 / 2' });
  const pending = effects; effects = []; pending.forEach(fn => fn());
}
async function flush() { await new Promise(resolve => setImmediate(resolve)); render(); }
function walk(node, out = []) {
  if (!node || typeof node !== 'object') return out;
  out.push(node); node.children.forEach(child => walk(child, out)); return out;
}
function button(label) {
  const found = walk(tree).find(n => n.tag === 'button' && n.children.includes(label));
  assert.ok(found, `missing button: ${label}`); return found;
}
function selectors() { return walk(tree).filter(n => n.tag === 'select'); }
render();
assert.equal(requests.length, 1);
requests.shift().resolve(start); await flush();
// A freshly decoded but equivalent RPC reference must not reset the session.
render(); assert.equal(requests.length, 0);
// Display requests must not serialize holes in partially selected fold inputs.
selectors()[2].props.onChange({ target: { value: '1' } }); render();
button('Refine display').props.onClick(); render();
const partialRefresh = requests.shift();
assert.deepEqual(plain(partialRefresh.params.inputs), []);
partialRefresh.resolve(start); await flush();
selectors()[1].props.onChange({ target: { value: '0' } }); render();
selectors()[2].props.onChange({ target: { value: '1' } }); render();
assert.equal(button('Preview folds').props.disabled, false);
button('Preview folds').props.onClick(); render();
const oldPreview = requests.shift();
assert.deepEqual(plain(oldPreview.params.inputs), [0, 1]);
// Changing an input invalidates even a successful late preview.
selectors()[2].props.onChange({ target: { value: '0' } }); render();
oldPreview.resolve({ ...start, view: { ...start.view, choices: [line(0, 0, 1, 0)] } });
await flush();
assert.ok(!walk(tree).some(n => n.tag === 'button' && n.children.includes('Use fold 1')));
// Refining an old snapshot must not revive a preview invalidated by changed inputs.
button('Refine display').props.onClick(); render();
requests.shift().resolve({ ...start, view: { ...start.view, choices: [line(0, 0, 1, 0)] } });
await flush();
assert.ok(!walk(tree).some(n => n.tag === 'button' && n.children.includes('Use fold 1')));
// Real choice buttons submit a snapshot reference and an index, never floats.
selectors()[2].props.onChange({ target: { value: '1' } }); render();
button('Preview folds').props.onClick(); render();
requests.shift().resolve({ ...start, session: { p: 'preview' }, view: { ...start.view, choices: [line(0, 0, 1, 0), line(1, 0, 1, 0)] } });
await flush();
assert.ok(button('Use fold 1'));
button('Use fold 2').props.onClick(); render();
const choice = requests.shift();
assert.equal(choice.params.session.p, 'preview'); assert.equal(choice.params.choice, 1);
choice.resolve({ session: { p: 'committed' }, view: { objects: [...start.view.objects, line(2, 0, 1, 0)], choices: [], steps: 1 } });
await flush();
// Undo stays enabled while another request is pending.
button('Submit').props.onClick(); render(); const oldSubmission = requests.shift();
assert.equal(button('Undo').props.disabled, false);
button('Undo').props.onClick(); render(); requests.shift().resolve(start); await flush();
oldSubmission.resolve({ ...start, edit: { textDocument: { uri: 'file:///proof.lean', version: 7 }, edits: [] }, proof: 'stale proof' });
await flush(); assert.ok(!walk(tree).some(n => n.children.includes('Insert checked proof')));
button('Submit').props.onClick(); render();
requests.shift().resolve({ ...start, edit: { textDocument: { uri: 'file:///proof.lean', version: 7 }, edits: [] }, proof: 'checked proof' });
await flush(); const insert = button('Insert checked proof');
await insert.props.onClick(); render(); assert.equal(edits.length, 1);
await insert.props.onClick(); render(); assert.equal(edits.length, 1);
assert.ok(walk(tree).some(n => n.props.role === 'alert' && n.children.some(c => String(c).includes('stale document'))));
console.log('PASS: panel input wiring, exact snapshot selection, undo during submission, and versioned insertion');
