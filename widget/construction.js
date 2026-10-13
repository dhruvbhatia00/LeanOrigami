import * as React from 'react';
import { useRpcSession, EditorContext, mapRpcError } from '@leanprover/infoview';

// All screen geometry is disposable. Only server-held exact object IDs are
// sent back to Lean. This module has no path from a mouse position to a fold.
const e = React.createElement;
const operations = [
  ['1', '1 · Through two points', ['First point', 'Second point'], ['point', 'point'], 'Make a crease through both selected points.'],
  ['2', '2 · Fold a point onto a point', ['Source point', 'Target point'], ['point', 'point'], 'Fold the source point exactly onto the target point. The crease lies halfway between them.'],
  ['3', '3 · Fold a line onto a line', ['Source line', 'Target line'], ['line', 'line'], 'Fold the whole source line onto the target line. Intersecting lines usually give two choices.'],
  ['4', '4 · Perpendicular through a point', ['Through point', 'Perpendicular to'], ['point', 'line'], 'Make a crease through the selected point, at a right angle to the selected line.'],
  ['5', '5 · Point onto line, through point', ['Source point', 'Fixed point', 'Target line'], ['point', 'point', 'line'], 'Keep the fixed point on the crease while folding the source point onto the target line.'],
  ['6', '6 · Two points onto two lines', ['First point', 'Second point', 'First target line', 'Second target line'], ['point', 'point', 'line', 'line'], 'In one fold, land the first point on the first target line and the second point on the second target line. There can be up to three choices.'],
  ['7', '7 · Point onto line, perpendicular', ['Source point', 'Target line', 'Perpendicular to'], ['point', 'line', 'line'], 'Fold the source point onto the target line, with the crease at a right angle to the reference line.'],
  ['intersection', 'Intersect two lines', ['First line', 'Second line'], ['line', 'line'], 'Add the crossing point of two existing lines. Parallel or coincident lines have no unique crossing.'],
];
const initialViewport = { x: 0.5, y: 0, width: 4 };
const HEIGHT = 360, WIDTH = 560;
export function bounds(viewport) {
  const h = viewport.width * HEIGHT / WIDTH;
  return [viewport.x - viewport.width / 2, viewport.x + viewport.width / 2,
    viewport.y - h / 2, viewport.y + h / 2];
}
// A bounded 1/2/5 grid remains legible throughout the permitted zoom range.
export function gridFor(viewport) {
  const box = bounds(viewport), rough = viewport.width / 8;
  const magnitude = 10 ** Math.floor(Math.log10(rough));
  const step = [1, 2, 5, 10].find(n => n * magnitude >= rough) * magnitude;
  const ticks = (lo, hi) => Array.from({ length: Math.max(0, Math.floor(hi / step) - Math.ceil(lo / step) + 1) },
    (_, i) => (Math.ceil(lo / step) + i) * step);
  return { step, xs: ticks(box[0], box[1]), ys: ticks(box[2], box[3]) };
}
// Six significant digits, without trailing zeros; tiny values stay nonzero.
const displayNumber = value => Number(value.toPrecision(6)).toString();
// Matches Lean Line.Contains: a*x + b*y = c.
export function clipLine(a, b, c, box) {
  if (![a, b, c, ...box].every(Number.isFinite) || (a === 0 && b === 0)) return null;
  const [xmin, xmax, ymin, ymax] = box, points = [];
  function add(x, y) {
    if (x >= xmin && x <= xmax && y >= ymin && y <= ymax &&
        !points.some(p => p[0] === x && p[1] === y)) points.push([x, y]);
  }
  if (b !== 0) { add(xmin, (c - a * xmin) / b); add(xmax, (c - a * xmax) / b); }
  if (a !== 0) { add((c - b * ymin) / a, ymin); add((c - b * ymax) / a, ymax); }
  return points.length >= 2 ? [points[0], points[points.length - 1]] : null;
}
export function precisionFor(width, extra = 0) {
  return Math.min(512, Math.max(32, Math.ceil(-Math.log2(width)) + 32 + extra));
}
export function visibleNumbers(object) {
  return object.values.map(v => Number(v.value));
}
export function describeObject(object) {
  const values = visibleNumbers(object).map(displayNumber);
  return object.kind === 'point' ? `(${values[0]}, ${values[1]})` :
    `${values[0]} x + ${values[1]} y = ${values[2]}`;
}
export function needsRefinement(object, viewport) {
  const pixel = viewport.width / WIDTH;
  return object.values.some(v => !Number.isFinite(Number(v.value)) ||
    !Number.isFinite(Number(v.error)) || Number(v.error) > pixel / 4);
}
// A generation token makes an old response harmless after undo or changed inputs.
export function newGeneration(ref) { return ++ref.current; }
export function isCurrent(ref, token) { return ref.current === token; }

export default function ConstructionPanel(props) {
  const rpc = useRpcSession(), editor = React.useContext(EditorContext);
  const [scene, setScene] = React.useState(null), sceneRef = React.useRef(null);
  const [operation, setOperation] = React.useState('1'), [inputs, setInputs] = React.useState([]);
  const [active, setActive] = React.useState(0), [viewport, setViewport] = React.useState(initialViewport);
  const [extraBits, setExtraBits] = React.useState(0), [busy, setBusy] = React.useState('');
  const [message, setMessage] = React.useState(''), [submission, setSubmission] = React.useState(null);
  const [finalPoint, setFinalPoint] = React.useState(1), [coordinate, setCoordinate] = React.useState('x');
  const [hover, setHover] = React.useState(null), [inspection, setInspection] = React.useState('');
  const [previewValid, setPreviewValid] = React.useState(false);
  const generation = React.useRef(0), drag = React.useRef(null), canvas = React.useRef(null);
  const gateKey = JSON.stringify(props.gate);
  const spec = operations.find(o => o[0] === operation), box = bounds(viewport);
  const objects = scene?.view.objects ?? [], choices = previewValid ? (scene?.view.choices ?? []) : [];
  const bits = precisionFor(viewport.width, extraBits);
  function install(result) { sceneRef.current = result; setScene(result); }
  async function request(action, overrides = {}) {
    const token = newGeneration(generation);
    setBusy(action === 'submit' ? 'Checking the complete proof…' : 'Computing…');
    setMessage(''); setSubmission(null);
    try {
      const response = await rpc.call('LeanOrigami.Widget.interact', {
        gate: props.gate, session: sceneRef.current?.session ?? null,
        action, operation, inputs: ['preview', 'intersect'].includes(action) ? inputs : [],
        choice: 0, point: finalPoint, coordinate, bits, ...overrides,
      });
      if (!isCurrent(generation, token)) return;
      install(response);
      if (action === 'preview') setPreviewValid(true);
      else if (['start', 'choose', 'intersect', 'undo'].includes(action)) {
        setPreviewValid(false); setInputs([]); setActive(0); setHover(null); setInspection('');
        if (action === 'start') {
          setFinalPoint(response.point ?? 1); setCoordinate(response.coordinate ?? 'x');
          setViewport(initialViewport);
        }
        if (action === 'intersect') setFinalPoint(response.view.objects.at(-1).index);
      }
      if (response.edit) setSubmission(response);
    } catch (error) {
      if (isCurrent(generation, token)) setMessage(mapRpcError(error).message);
    } finally { if (isCurrent(generation, token)) setBusy(''); }
  }
  React.useEffect(() => {
    newGeneration(generation); install(null); setInputs([]); setSubmission(null);
    request('start');
    return () => { newGeneration(generation); };
  }, [gateKey]);
  // React delegates wheel events passively. A native non-passive listener is
  // required to consume the gesture instead of also scrolling the infoview.
  React.useEffect(() => {
    const element = canvas.current;
    if (!element) return;
    const wheel = ev => {
      ev.preventDefault(); ev.stopPropagation();
      setViewport(v => ({ ...v, width: Math.min(1e12, Math.max(1e-12,
        v.width * (ev.deltaY > 0 ? 1.2 : 1 / 1.2))) }));
    };
    element.addEventListener('wheel', wheel, { passive: false });
    return () => element.removeEventListener('wheel', wheel);
  }, []);
  // Refresh display only; the RPC preserves exact choices and program contents.
  React.useEffect(() => {
    if (sceneRef.current && !busy) request('render');
  }, [bits]);
  function invalidate() {
    newGeneration(generation); setBusy(''); setSubmission(null); setMessage(''); setPreviewValid(false);
    if (sceneRef.current) install({ ...sceneRef.current, view: { ...sceneRef.current.view, choices: [] } });
  }
  function select(index, kind) {
    if (spec[3][active] !== kind) { setMessage(`Choose a ${spec[3][active]} for ${spec[2][active]}.`); return; }
    invalidate(); setInputs(old => { const next = [...old]; next[active] = index; return next; });
    setActive(Math.min(active + 1, spec[2].length - 1));
  }
  function screen([x, y]) {
    return [(x - box[0]) / viewport.width * WIDTH, HEIGHT - (y - box[2]) / viewport.width * WIDTH];
  }
  function draw(object, candidate) {
    const values = visibleNumbers(object), selected = !candidate && inputs.includes(object.index);
    const color = candidate ? '#e87925' : selected ? '#4ea1ff' : 'currentColor';
    const key = `${candidate ? 'c' : 'o'}${object.index}`;
    const title = `${candidate ? 'Choice' : object.kind} ${object.index + (candidate ? 1 : 0)}: ≈ ${describeObject(object)}`;
    const inspect = { onMouseEnter: () => { setInspection(title); if (candidate) setHover(object.index); },
      onMouseLeave: () => { setInspection(''); if (candidate) setHover(null); } };
    if (object.kind === 'point') {
      const [cx, cy] = screen(values);
      if (![cx, cy].every(Number.isFinite)) return null;
      return e('g', { key, ...inspect, onClick: () => select(object.index, 'point'), style: { cursor: 'pointer' } },
        e('title', null, title), e('circle', { cx, cy, r: 12, fill: 'transparent' }),
        e('circle', { cx, cy, r: 4, fill: color }), e('text', { x: cx + 7, y: cy - 7, fill: color, fontSize: 12 }, `P${object.index}`));
    }
    const segment = clipLine(...values, box);
    if (!segment) return null;
    const [p, q] = segment.map(screen);
    // Anchor labels inside the clipped segment, then keep their text inside
    // the viewport even for horizontal/vertical lines at the canvas edge.
    const labelX = Math.max(6, Math.min(WIDTH - 60, p[0] * 0.8 + q[0] * 0.2 + 6));
    const labelY = Math.max(14, Math.min(HEIGHT - 6, p[1] * 0.8 + q[1] * 0.2 - 6));
    return e('g', { key, ...inspect, onClick: () => candidate ? setHover(object.index) : select(object.index, 'line'), style: { cursor: 'pointer' } },
      e('title', null, title), e('line', { x1: p[0], y1: p[1], x2: q[0], y2: q[1], stroke: 'transparent', strokeWidth: 12 }),
      e('line', { x1: p[0], y1: p[1], x2: q[0], y2: q[1], stroke: color,
        strokeWidth: candidate && hover === object.index ? 4 : 1.5, strokeDasharray: candidate ? '7 4' : undefined }),
      e('text', { x: labelX, y: labelY, fill: color, fontSize: 12,
        stroke: 'var(--vscode-editor-background)', strokeWidth: 3, paintOrder: 'stroke' },
        candidate ? `Choice ${object.index + 1}` : `L${object.index}`));
  }
  const grid = gridFor(viewport);
  const gridLines = [
    ...grid.xs.map(x => {
      const [sx] = screen([x, 0]);
      return e('g', { key: `x${x}` },
        e('line', { x1: sx, x2: sx, y1: 0, y2: HEIGHT, strokeWidth: x === 0 ? 1.3 : 0.6 }),
        e('text', { x: sx + 3, y: HEIGHT - 5, stroke: 'none' }, displayNumber(x)));
    }),
    ...grid.ys.map(y => {
      const [, sy] = screen([0, y]);
      return e('g', { key: `y${y}` },
        e('line', { x1: 0, x2: WIDTH, y1: sy, y2: sy, strokeWidth: y === 0 ? 1.3 : 0.6 }),
        e('text', { x: 4, y: Math.max(11, sy - 3), stroke: 'none' }, displayNumber(y)));
    }),
  ];
  const button = (label, onClick, disabled = false) => e('button', { type: 'button', onClick, disabled, style: { margin: '3px' } }, label);
  const unresolvedDisplay = [...objects, ...choices].some(o => needsRefinement(o, viewport));
  return e('details', { open: true, style: { maxWidth: '760px' } },
    e('summary', null, 'Origami construction'),
    e('p', null, `Goal: ${props.target}`),
    props.saved && e('p', null, 'Saved construction. Changes are drafts until you save them.'),
    e('svg', { ref: canvas, viewBox: `0 0 ${WIDTH} ${HEIGHT}`, role: 'img', 'aria-label': 'Origami construction canvas',
      style: { width: '100%', border: '1px solid currentColor', touchAction: 'none', background: 'var(--vscode-editor-background)' },
      onPointerDown: ev => { if (ev.target === ev.currentTarget) { drag.current = { x: ev.clientX, y: ev.clientY, viewport }; ev.currentTarget.setPointerCapture(ev.pointerId); } },
      onPointerMove: ev => { if (drag.current) { const d = drag.current, scale = d.viewport.width / ev.currentTarget.getBoundingClientRect().width;
        setViewport({ ...d.viewport, x: d.viewport.x - (ev.clientX - d.x) * scale, y: d.viewport.y + (ev.clientY - d.y) * scale }); } },
      onPointerUp: () => { drag.current = null; }, onPointerCancel: () => { drag.current = null; },
    }, e('g', { pointerEvents: 'none', stroke: 'currentColor', fill: 'currentColor', strokeOpacity: 0.2, fillOpacity: 0.65, fontSize: 10 }, ...gridLines),
      ...objects.filter(o => o.kind === 'line').map(o => draw(o, false)),
      ...choices.map(o => draw(o, true)),
      ...objects.filter(o => o.kind === 'point').map(o => draw(o, false))),
    e('p', { role: 'status', style: { minHeight: '2.5em', margin: '6px 0', fontSize: '0.9em' } },
      inspection || 'Hover over a point or line to inspect its approximate coordinates or equation.'),
    e('div', null,
      button('Zoom in', () => setViewport(v => ({ ...v, width: Math.max(1e-12, v.width / 2) }))),
      button('Zoom out', () => setViewport(v => ({ ...v, width: Math.min(1e12, v.width * 2) }))),
      button('Reset view', () => setViewport(initialViewport)),
      button('Refine display', () => setExtraBits(b => Math.min(480, b + 32)), !!busy),
      button('Undo', () => request('undo'), !scene || scene.view.steps === 0)),
    unresolvedDisplay && e('p', { role: 'status' }, 'Some objects need more display precision. Refine or use the exact object list.'),
    e('label', null, 'Operation ', e('select', { value: operation, onChange: ev => { invalidate(); setOperation(ev.target.value); setInputs([]); setActive(0); } },
      ...operations.map(o => e('option', { key: o[0], value: o[0] }, o[1])))),
    e('p', { style: { margin: '6px 0' } }, spec[4]),
    e('p', { style: { margin: '6px 0', fontSize: '0.9em' } },
      `Click a ${spec[3][active]} on the drawing for “${spec[2][active]}”, or use the dropdowns. Drag empty space to pan; scroll to zoom.`),
    ...spec[2].map((role, i) => e('label', { key: i, style: { display: 'block', margin: '5px 0' } }, `${role} `,
      e('select', { value: inputs[i] ?? '', onFocus: () => setActive(i), onChange: ev => { invalidate(); setInputs(old => { const next = [...old]; next[i] = Number(ev.target.value); return next; }); } },
        e('option', { value: '', disabled: true }, `Select a ${spec[3][i]}`),
        ...objects.filter(o => o.kind === spec[3][i]).map(o => e('option', { key: o.index, value: o.index }, `${o.kind} ${o.index}`))))),
    button(operation === 'intersection' ? 'Add intersection' : 'Preview folds', () => request(operation === 'intersection' ? 'intersect' : 'preview'),
      !!busy || spec[2].some((_, i) => inputs[i] === undefined)),
    choices.length > 0 && e('div', null, e('p', null, `${choices.length} exact choice(s). Select by number if previews overlap.`),
      ...choices.map(o => e('div', { key: o.index, onMouseEnter: () => setHover(o.index), onMouseLeave: () => setHover(null) },
        button(`Use fold ${o.index + 1}`, () => request('choose', { choice: o.index }), !!busy),
        e('small', null, describeObject(o))))),
    e('details', null, e('summary', null, `Objects · ${scene?.view.steps ?? 0} construction steps`),
      e('ul', null, ...objects.map(o => e('li', { key: o.index },
        button(`${o.kind} ${o.index}`, () => select(o.index, o.kind)),
        e('span', null, describeObject(o)))))),
    e('details', null, e('summary', null, 'Construction history'),
      e('ol', null, ...(scene?.view.history ?? []).map((step, i) => e('li', { key: i }, `${step} → object ${i + 2}`)))),
    e('fieldset', null, e('legend', null, 'Submit a coordinate'),
      e('select', { 'aria-label': 'Final point', value: objects.some(o => o.kind === 'point' && o.index === finalPoint) ? finalPoint : '', onChange: ev => { invalidate(); setFinalPoint(Number(ev.target.value)); } },
        e('option', { value: '', disabled: true }, 'Select a point'),
        ...objects.filter(o => o.kind === 'point').map(o => e('option', { key: o.index, value: o.index }, `Point ${o.index}`))),
      e('select', { 'aria-label': 'Coordinate', value: coordinate, onChange: ev => { invalidate(); setCoordinate(ev.target.value); } },
        e('option', { value: 'x' }, 'x coordinate'), e('option', { value: 'y' }, 'y coordinate')),
      button('Submit', () => request('submit'), !!busy || !scene || !objects.some(o => o.kind === 'point' && o.index === finalPoint))),
    busy && e('p', { role: 'status' }, busy), message && e('p', { role: 'alert' }, message),
    submission && e('div', null, e('p', null, 'Lean checked this proof against the original goal.'),
      button('Save construction', async () => { try {
        await editor.api.applyEdit({ documentChanges: [submission.edit] });
        setSubmission(null);
      } catch (err) { setMessage(`The source changed or saving failed: ${String(err)}`); } }),
      e('details', null, e('summary', null, 'Saved construction source'), e('pre', { style: { overflow: 'auto', maxHeight: '240px' } }, submission.source))));
}
