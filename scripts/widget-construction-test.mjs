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
const { describeObject, gridFor, clipLine, precisionFor, needsRefinement, newGeneration, isCurrent } = module.namespace;
const plain = x => JSON.parse(JSON.stringify(x));
assert.deepEqual(plain(clipLine(1, 0, 1, [-2, 2, -2, 2])), [[1, -2], [1, 2]]);
assert.deepEqual(plain(clipLine(0, 1, 0, [-2, 2, -2, 2])), [[-2, 0], [2, 0]]);
assert.equal(clipLine(0, 0, 0, [-2, 2, -2, 2]), null);
assert.equal(clipLine(1, 0, 5, [-2, 2, -2, 2]), null);
assert.ok(precisionFor(1e-10) > precisionFor(4));
assert.equal(precisionFor(1e-200, 480), 512);
assert.ok(needsRefinement({ values: [{ value: '1.4', error: '0.1' }] }, { width: 4 }));
assert.ok(!needsRefinement({ values: [{ value: '1.4', error: '1e-30' }] }, { width: 4 }));
for (const width of [1e-12, 4, 1e12]) {
  const grid = gridFor({ x: 0, y: 0, width });
  assert.ok(grid.step > 0 && Number.isFinite(grid.step));
  assert.ok(grid.xs.length > 1 && grid.xs.length <= 10);
  assert.ok(grid.ys.length > 1 && grid.ys.length <= 10);
  assert.ok(grid.xs.includes(0) && grid.ys.includes(0));
}
const ref = { current: 0 };
const preview = newGeneration(ref), undo = newGeneration(ref);
assert.ok(!isCurrent(ref, preview));
assert.ok(isCurrent(ref, undo));
console.log('PASS: implicit-line clipping, vertical lines, precision, and stale-reply rejection');

// Render the actual component with a small deterministic React/editor adapter.
// This tests event wiring, not browser layout or the Lean RPC implementation.
let slots = [], cursor = 0, effects = [], tree, requests = [], edits = [];
let rpc, editor, gate = 'goal', panelProps = {};
const listeners = new Map();
const canvas = {
  addEventListener(name, callback, options) { listeners.set(name, { callback, options }); },
  removeEventListener(name, callback) {
    if (listeners.get(name)?.callback === callback) listeners.delete(name);
  },
};
const react = {
  createElement: (tag, props, ...children) => {
    if (tag === 'svg' && props.ref) props.ref.current = canvas;
    return { tag, props: props ?? {}, children: children.flat(Infinity) };
  },
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
// Hover descriptions and object lists share concise approximate formatting.
assert.equal(describeObject(point(0, 1, -0)), '(1, 0)');
assert.equal(describeObject(point(0, Math.sqrt(2), -1 / 3)), '(1.41421, -0.333333)');
assert.equal(describeObject(line(2, 1, -2, 0.5)), '1 x + -2 y = 0.5');
assert.equal(describeObject(point(0, 1e-12, 1e24)), '(1e-12, 1e+24)');
const start = { session: { p: 'initial' }, view: { objects: [point(0, 0, 0), point(1, 1, 0)], choices: [], steps: 0 } };
rpc = { call(name, params) {
  // Lean's RPC decoder requires fields even when their structure has defaults.
  assert.equal(typeof params.recipeName, 'string');
  assert.ok(Array.isArray(params.sampleInputs));
  assert.equal(typeof params.requirement.family, 'string');
  assert.ok(Array.isArray(params.requirement.references));
  assert.ok(Array.isArray(params.requirement.values));
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
  tree = uiModule.namespace.default({ gate: { p: gate }, target: '1 / 2', ...panelProps });
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
function selectors() { return walk(tree).filter(n => n.tag === 'select' && !n.props['aria-label']?.startsWith('Requirement')); }
render();
assert.equal(requests.length, 1);
requests.shift().resolve(start); await flush();
// Wheel zoom consumes the gesture: the outer infoview must not also scroll.
assert.equal(listeners.get('wheel').options.passive, false);
let prevented = false, stopped = false;
listeners.get('wheel').callback({ deltaY: 1,
  preventDefault() { prevented = true; }, stopPropagation() { stopped = true; } });
render();
assert.ok(prevented && stopped);
assert.equal(walk(tree).find(n => n.tag === 'svg').props.onWheel, undefined);
// Object hover exposes coordinates, with approximation clearly labelled.
walk(tree).find(n => n.tag === 'g' && n.props.key === 'o1').props.onMouseEnter(); render();
assert.ok(walk(tree).some(n => n.props.role === 'status' && n.children.some(c => String(c).includes('point 1: ≈'))));
walk(tree).find(n => n.tag === 'g' && n.props.key === 'o1').props.onMouseLeave(); render();
assert.ok(walk(tree).some(n => n.children.some(c => String(c).includes('Click a point on the drawing'))));
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
assert.ok(walk(tree).some(n => n.tag === 'text' && n.children.includes('Choice 2')));
button('Use fold 2').props.onClick(); render();
const choice = requests.shift();
assert.equal(choice.params.session.p, 'preview'); assert.equal(choice.params.choice, 1);
choice.resolve({ session: { p: 'committed' }, view: { objects: [...start.view.objects, line(2, 0, 1, 0)], choices: [], steps: 1 } });
await flush();
// Visible line labels use the same stable reference as the input controls.
const lineLabel = walk(tree).find(n => n.tag === 'text' && n.children.includes('L2'));
assert.ok(lineLabel);
assert.ok(lineLabel.props.x >= 0 && lineLabel.props.x <= 560);
assert.ok(lineLabel.props.y >= 0 && lineLabel.props.y <= 360);
// A committed fold starts the next canvas selection at the first role.
walk(tree).find(n => n.tag === 'g' && n.props.key === 'o0').props.onClick(); render();
assert.equal(selectors()[1].props.value, 0);
assert.equal(selectors()[2].props.value, '');
// Undo stays enabled while another request is pending.
button('Submit').props.onClick(); render(); const oldSubmission = requests.shift();
assert.equal(button('Undo').props.disabled, false);
button('Undo').props.onClick(); render(); requests.shift().resolve(start); await flush();
oldSubmission.resolve({ ...start, edit: { textDocument: { uri: 'file:///proof.lean', version: 7 }, edits: [] }, source: 'stale certificate' });
await flush(); assert.ok(!walk(tree).some(n => n.children.includes('Save construction')));
button('Submit').props.onClick(); render();
requests.shift().resolve({ ...start, edit: { textDocument: { uri: 'file:///proof.lean', version: 7 }, edits: [] }, source: 'checked certificate' });
await flush(); const insert = button('Save construction');
await insert.props.onClick(); render(); assert.equal(edits.length, 1);
await insert.props.onClick(); render(); assert.equal(edits.length, 1);
assert.ok(walk(tree).some(n => n.props.role === 'alert' && n.children.some(c => String(c).includes('stale document'))));
// Reopening a saved tactic loads its program and its submitted coordinate.
gate = 'saved-goal'; render();
assert.equal(requests.length, 1);
assert.equal(requests[0].params.action, 'start');
assert.equal(requests[0].params.session, null);
requests.shift().resolve({ session: { p: 'restored' }, point: 4, coordinate: 'y',
  view: { objects: [...start.view.objects, line(2, 1, 0, 0), line(3, 0, 1, 1), point(4, 0, 1)],
    choices: [], steps: 3, history: [
      { description: 'first fold', inputs: [0, 1], output: 2 },
      { description: 'second fold', inputs: [0, 2], output: 3 },
      { description: 'intersection', inputs: [2, 3], output: 4 }] } });
await flush();
assert.equal(selectors().find(n => n.props['aria-label'] === 'Final point').props.value, 4);
assert.equal(selectors().find(n => n.props['aria-label'] === 'Coordinate').props.value, 'y');
assert.equal(button('Undo').props.disabled, false);
const historyRows = () => walk(tree).filter(n => n.tag === 'li' && n.props.tabIndex === 0);
const drawn = index => walk(tree).find(n => n.tag === 'g' && n.props.key === `o${index}`);
selectors()[1].props.onChange({ target: { value: '1' } }); render();
selectors()[2].props.onChange({ target: { value: '0' } }); render();
const savedSelections = selectors().map(n => n.props.value);
historyRows()[0].props.onMouseMove(); render();
assert.equal(drawn(0).props['data-history-role'], 'input');
assert.equal(drawn(1).props['data-history-role'], 'input');
assert.equal(drawn(2).props['data-history-role'], 'output');
assert.equal(drawn(3).props.style.opacity, 0.2);
// Draw the output last so coincident earlier objects cannot cover it.
assert.equal(walk(tree).filter(n => n.tag === 'g' && /^o/.test(n.props.key)).at(-1).props.key, 'o2');
assert.ok(walk(tree).some(n => n.props.role === 'status' && n.children.some(c => String(c).includes('Inputs (blue): P0, P1. Output (orange): L2'))));
assert.deepEqual(selectors().map(n => n.props.value), savedSelections);
assert.equal(requests.length, 0); // Inspection is local and never runs an operation.
historyRows()[0].props.onMouseLeave(); render();
assert.equal(drawn(2).props['data-history-role'], null);
assert.equal(drawn(3).props.style.opacity, 1);
historyRows()[2].props.onFocus(); render();
// Scrolling a focused row into view must not let a stationary pointer steal it.
assert.equal(historyRows()[0].props.onMouseEnter, undefined);
historyRows()[0].props.onMouseLeave(); render();
assert.equal(drawn(2).props['data-history-role'], 'input');
assert.equal(drawn(3).props['data-history-role'], 'input');
assert.equal(drawn(4).props['data-history-role'], 'output');
assert.equal(walk(drawn(4)).find(n => n.tag === 'circle' && n.props.fill !== 'transparent').props.r, 6);
historyRows()[2].props.onBlur(); render();
assert.equal(drawn(4).props['data-history-role'], null);
historyRows()[0].props.onFocus(); render();
walk(tree).find(n => n.tag === 'details' && n.props.onToggle).props.onToggle({ currentTarget: { open: false } }); render();
assert.equal(drawn(2).props['data-history-role'], null);
button('Submit').props.onClick(); render();
const restoredSubmit = requests.shift();
assert.equal(restoredSubmit.params.session.p, 'restored');
assert.equal(restoredSubmit.params.point, 4);
assert.equal(restoredSubmit.params.coordinate, 'y');
restoredSubmit.reject(new Error('test cleanup')); await flush();
historyRows()[2].props.onMouseMove(); render();
button('Undo').props.onClick(); render(); requests.shift().resolve(start); await flush();
assert.equal(historyRows().length, 0);
assert.equal(drawn(0).props['data-history-role'], null);
assert.equal(drawn(0).props.style.opacity, 1);
console.log('PASS: panel input wiring, exact snapshot selection, undo during submission, and versioned insertion');

// Standalone mode shares the same renderer, but never promises a proved goal.
panelProps = { workspace: true, recipes: [{ id: 'recipe:midpoint', name: 'Midpoint',
  parameters: [{ name: 'A', kind: 'point' }, { name: 'B', kind: 'point' }] }] };
gate = 'workspace'; render(); requests.shift().resolve(start); await flush();
assert.ok(!selectors().some(n => n.props['aria-label'] === 'Coordinate'));
assert.ok(selectors().some(n => n.props['aria-label'] === 'Recipe output'));
selectors()[0].props.onChange({ target: { value: 'recipe:midpoint' } }); render();
selectors()[1].props.onChange({ target: { value: '0' } }); render();
selectors()[2].props.onChange({ target: { value: '1' } }); render();
button('Run recipe').props.onClick(); render();
const invocation = requests.shift();
assert.equal(invocation.params.action, 'recipe');
assert.deepEqual(plain(invocation.params.inputs), [0, 1]);
const grouped = { ...start, view: { objects: [...start.view.objects, line(2, 0, 1, 0),
  line(3, 1, 0, 0.5), point(4, 0.5, 0)], steps: 3, choices: [], result: 4,
  history: [{ description: 'join', inputs: [0, 1], output: 2 },
    { description: 'bisect', inputs: [0, 1], output: 3 },
    { description: 'intersect', inputs: [2, 3], output: 4 }],
  groups: [{ name: 'My recipe', start: 0, count: 3, inputs: [0, 1], output: 4 },
    { name: 'Midpoint', start: 0, count: 3, inputs: [0, 1], output: 4 }] } };
invocation.resolve(grouped); await flush();
assert.equal(selectors().find(n => n.props['aria-label'] === 'Recipe output').props.value, 4);
assert.ok(walk(tree).some(n => n.tag === 'summary' && n.children.includes('Midpoint (P0, P1) → P4')));
assert.equal(historyRows().length, 3);
assert.ok(walk(tree).some(n => n.tag === 'summary' && n.children.includes('My recipe (P0, P1) → P4')));
walk(tree).find(n => n.tag === 'summary' && n.children.includes('My recipe (P0, P1) → P4')).props.onFocus(); render();
assert.equal(drawn(0).props['data-history-role'], 'input');
assert.equal(drawn(1).props['data-history-role'], 'input');
assert.equal(drawn(4).props['data-history-role'], 'output');
historyRows()[2].props.onFocus(); render();
assert.equal(drawn(4).props['data-history-role'], 'output');
assert.equal(drawn(2).props['data-history-role'], 'input');
assert.equal(requests.length, 0);
button('Prepare recipe').props.onClick(); render();
requests.shift().resolve({ ...grouped, source: 'recipe data', edit: {} }); await flush();
assert.ok(button('Save recipe'));
assert.ok(!walk(tree).some(n => n.children.includes('Lean checked this proof against the original goal.')));
// A pending branch cannot be accidentally invalidated by changing inputs.
button('Run recipe').props.onClick(); render();
requests.shift().resolve({ ...grouped, view: { ...grouped.view, running: true,
  choices: [line(0, 1, 1, 0), line(1, 1, -1, 0)] } }); await flush();
assert.ok(button('Prepare recipe').props.disabled);
assert.ok(selectors()[0].props.disabled);
assert.ok(button('Use fold 1'));
button('Cancel recipe').props.onClick(); render();
assert.equal(requests[0].params.action, 'undo');
requests.shift().resolve(start); await flush();
assert.ok(!walk(tree).some(n => n.children.includes('Cancel recipe')));
console.log('PASS: standalone recipe controls, invocation arguments, grouped history, and branch cancellation');

// Bare-command setup, exact grid values, sample editing, and failed replay recovery.
assert.equal(module.namespace.snapSample(0.49, 0.5), '5/10');
assert.equal(module.namespace.snapSample(-1.01, 0.2), '-10/10');
assert.equal(module.namespace.snapSample(21, 10), '20');
assert.throws(() => module.namespace.snapSample(1e100, 1), /origin/);
assert.deepEqual(plain(module.namespace.samplePreview([{ name: 'A', kind: 'point', values: ['1/2', '-2'], keep: false }], [])), [point(0, 0.5, -2)]);
const exactRows = [{ name: 'A', kind: 'point', values: ['0', '0'], keep: true },
  { name: 'B', kind: 'point', values: ['1', '0'], keep: true }];
gate = 'bare'; render(); requests.shift().resolve({ ...start,
  view: { objects: [], choices: [], steps: 0 }, workspace: { name: '', inputs: [], ready: false, nameLocked: false } }); await flush();
assert.ok(button('Start construction').props.disabled);
assert.ok(!walk(tree).some(n => n.tag === 'button' && n.children.includes('Prepare recipe')));
button('Add point input').props.onClick(); render();
function input(label) { const node = walk(tree).find(n => n.tag === 'input' && n.props['aria-label'] === label); assert.ok(node, label); return node; }
assert.equal(input('Input 0 name').props.value, 'A');
input('Recipe name').props.onChange({ target: { value: 'myRecipe' } }); render();
input('Input 0 name').props.onChange({ target: { value: 'A' } }); render();
input('Input 0 x').props.onChange({ target: { value: '1/2' } }); render();
button('Start construction').props.onClick(); render();
assert.equal(requests[0].params.action, 'samples');
assert.equal(requests[0].params.recipeName, 'myRecipe');
assert.equal(requests[0].params.sampleInputs[0].values[0], '1/2');
const workspace = { name: 'myRecipe', inputs: exactRows, ready: true, nameLocked: false };
requests.shift().resolve({ ...start, workspace }); await flush();
assert.ok(button('Edit samples'));
assert.ok(button('Prepare recipe'));
button('Edit samples').props.onClick(); render();
assert.ok(!walk(tree).some(n => n.tag === 'button' && n.children.includes('Prepare recipe')));
input('Input 1 x').props.onChange({ target: { value: '0' } }); render();
button('Apply samples').props.onClick(); render();
assert.equal(requests[0].params.sampleInputs[0].keep, true);
assert.equal(requests[0].params.sampleInputs[1].keep, false);
requests.shift().resolve({ ...start, workspace, view: { ...start.view,
  running: true, failure: 'Step 1: Choose two distinct points.' } }); await flush();
assert.ok(walk(tree).some(n => n.props.role === 'alert' && String(n.children).includes('Step 1')));
assert.ok(button('Apply samples'));
button('Reset samples').props.onClick(); render();
assert.equal(requests[0].params.action, 'resetSamples');
requests.shift().resolve({ ...grouped, workspace }); await flush();
button('Finish editing samples').props.onClick(); render();
assert.ok(!button('Prepare recipe').props.disabled);
console.log('PASS: bare setup, rational sample edits, preserved inputs, failure recovery, and reset controls');

canvas.getBoundingClientRect = () => ({ left: 0, top: 0, width: 560, height: 360 });
canvas.setPointerCapture = () => {};
button('Edit samples').props.onClick(); render();
drawn(0).props.onPointerDown({ stopPropagation() {}, pointerId: 1 }); render();
let svg = walk(tree).find(n => n.tag === 'svg');
svg.props.onPointerMove({ clientX: 280, clientY: 180 }); render();
svg = walk(tree).find(n => n.tag === 'svg');
svg.props.onPointerUp({ clientX: 280, clientY: 180 }); render();
assert.equal(requests[0].params.action, 'samples');
assert.deepEqual(plain(requests[0].params.sampleInputs[0].values), ['5/10', '0/10']);
requests.shift().resolve({ ...grouped, workspace }); await flush();
// Two placement clicks describe a line input, not two additional point inputs.
gate = 'line-setup'; render(); requests.shift().resolve({ ...start,
  view: { objects: [], choices: [], steps: 0 }, workspace: { name: '', inputs: [], ready: false, nameLocked: false } }); await flush();
button('Add line input').props.onClick(); render();
assert.equal(input('Input 0 name').props.value, 'ℓ₁');
input('Recipe name').props.onChange({ target: { value: 'lineRecipe' } }); render();
input('Input 0 name').props.onChange({ target: { value: 'L' } }); render();
button('Place L').props.onClick(); render();
const clickCanvas = (x, y) => {
  const svg = walk(tree).find(n => n.tag === 'svg');
  svg.props.onPointerDown({ clientX: x, clientY: y, target: canvas, currentTarget: canvas }); render();
};
clickCanvas(210, 180); clickCanvas(350, 180);
button('Start construction').props.onClick(); render();
assert.equal(requests[0].params.sampleInputs.length, 1);
assert.equal(requests[0].params.sampleInputs[0].kind, 'line');
assert.deepEqual(plain(requests[0].params.sampleInputs[0].values), ['0/10', '0/10', '10/10', '0/10']);
requests.shift().reject(new Error('test cleanup')); await flush();
console.log('PASS: point drag replays on release and two-click line placement creates one input');

// Naming is deterministic, skips manual names of either kind, and reuses gaps.
const { defaultSampleName } = module.namespace;
assert.equal(defaultSampleName([], 'point'), 'A');
assert.equal(defaultSampleName([{ name: 'A' }, { name: 'C' }], 'point'), 'B');
assert.equal(defaultSampleName([{ name: 'ℓ₁' }, { name: 'ℓ₃' }], 'line'), 'ℓ₂');
assert.equal(defaultSampleName(Array.from({ length: 26 }, (_, n) => ({ name: String.fromCharCode(65 + n) })), 'point'), 'AA');
render();
const resetHelp = walk(tree).find(n => n.tag === 'button' && n.children.includes('Reset view'));
assert.match(resetHelp.props.title, /camera position and zoom/);
resetHelp.props.onFocus(); render();
assert.ok(walk(tree).find(n => n.props.role === 'tooltip').children.includes(resetHelp.props.title));
resetHelp.props.onBlur(); render();
const refineHelp = walk(tree).find(n => n.tag === 'button' && n.children.includes('Refine display'));
refineHelp.props.onMouseEnter(); render();
assert.match(walk(tree).find(n => n.props.role === 'tooltip').children.join(''), /exact construction and proof stay the same/);
refineHelp.props.onMouseLeave(); render();
console.log('PASS: automatic names, collisions, and hover/keyboard control explanations');

// Requirements are server checks, with editable inputs separated from inherited checks.
gate = 'requirements'; render(); requests.shift().resolve({ ...grouped, workspace: { ...workspace,
  requirements: [{ description: 'A.y = 0', status: 'Satisfied' }],
  nestedRequirements: [{ description: 'not (object 0 = object 1)', status: 'Satisfied' }] } }); await flush();
const requirementSection = walk(tree).find(n => n.props['aria-label'] === 'Requirements');
const requirementKeys = requirementSection.children.filter(n => n && typeof n === 'object' && n.props.key !== undefined).map(n => n.props.key);
assert.equal(new Set(requirementKeys).size, requirementKeys.length, 'inherited rows and input controls need distinct React keys');
const selectRequirement = label => walk(tree).find(n => n.tag === 'select' && n.props['aria-label'] === label);
assert.ok(button('Add requirement').props.disabled);
selectRequirement('Requirement family').props.onChange({ target: { value: 'onXAxis' } }); render();
selectRequirement('Requirement input 1').props.onChange({ target: { value: '1' } }); render();
button('Add requirement').props.onClick(); render();
assert.equal(requests[0].params.action, 'addRequirement');
assert.deepEqual(plain(requests[0].params.requirement.references), [1]);
assert.equal(requests[0].params.requirement.family, 'onXAxis');
const failedRequirement = { ...grouped, workspace: { ...workspace, replaying: true,
  requirements: [{ description: 'A.y = 0', status: 'Not satisfied' }] },
  view: { ...start.view, running: true, failure: 'Requirement failed: A.y = 0' } };
requests.shift().resolve(failedRequirement); await flush();
assert.ok(!button('Remove requirement 1').props.disabled);
button('Remove requirement 1').props.onClick(); render();
assert.equal(requests[0].params.action, 'removeRequirement');
assert.equal(requests[0].params.choice, 0);
requests.shift().resolve({ ...grouped, workspace }); await flush();
assert.ok(!button('Prepare recipe').props.disabled);
console.log('PASS: requirement form, exact-check failure display, and removal while replay is blocked');
