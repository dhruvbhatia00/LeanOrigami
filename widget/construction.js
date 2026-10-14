import * as React from 'react';
import { useRpcSession, EditorContext, mapRpcError } from '@leanprover/infoview';

// All screen geometry is disposable. Only server-held exact object IDs are
// sent back to Lean for folds. Sample placement is separate: rational grid
// values are validated by Lean and can never supply proof seeds.
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
// Geometry families all compile on the server to the proved condition checker.
const requirementFamilies = [
  ['distinctPoints', 'Distinct points', ['point', 'point']], ['samePoints', 'Same point', ['point', 'point']],
  ['distinctLines', 'Distinct lines', ['line', 'line']], ['sameLines', 'Same line', ['line', 'line']],
  ['onLine', 'Point on line', ['point', 'line']], ['onXAxis', 'Point on x-axis', ['point']], ['onYAxis', 'Point on y-axis', ['point']],
  ['collinear', 'Collinear points (repeated points allowed)', ['point', 'point', 'point']],
  ['parallel', 'Parallel lines (coincident allowed)', ['line', 'line']], ['perpendicular', 'Perpendicular lines', ['line', 'line']],
  ['coordinateEq', 'Coordinate = value', ['point']], ['coordinateLe', 'Coordinate ≤ value', ['point']],
  ['coordinateLt', 'Coordinate < value', ['point']], ['coordinateGe', 'Coordinate ≥ value', ['point']], ['coordinateGt', 'Coordinate > value', ['point']],
  ['polynomialEq', 'Polynomial = 0', ['point']], ['polynomialLe', 'Polynomial ≤ 0', ['point']], ['polynomialLt', 'Polynomial < 0', ['point']],
  ['and', 'Combine requirements: AND', ['requirement', 'requirement']],
  ['or', 'Combine requirements: OR', ['requirement', 'requirement']], ['not', 'Negate a requirement', ['requirement']],
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

// Convert the chosen grid multiple to an exact fraction, not a float literal.
export function snapSample(value, step) {
  const index = Math.round(value / step);
  if (!Number.isSafeInteger(index)) throw new Error('Pan closer to the origin to place a sample.');
  const [mantissa, exponent] = step.toExponential(0).split('e');
  const power = Number(exponent), scale = 10n ** BigInt(Math.abs(power));
  const numerator = BigInt(index) * BigInt(mantissa);
  return power >= 0 ? String(numerator * scale) : `${numerator}/${scale}`;
}

// These numbers draw an unsaved placement only. The server parses the strings
// independently as rationals before using them as exact workspace samples.
export function samplePreview(rows, existing) {
  const number = text => { const [n, d = '1'] = text.split('/'); return Number(n) / Number(d); };
  return rows.flatMap((row, index) => {
    if (row.keep) return existing.filter(o => o.index === index);
    let values = row.values.map(number);
    if (row.values.some(v => !v.trim()) || !values.every(Number.isFinite)) return [];
    if (row.kind === 'line' && values.length === 4) {
      const [x, y, u, v] = values, a = y - v, b = u - x; values = [a, b, a * x + b * y];
    }
    return [{ index, kind: row.kind, values: values.map(value => ({ value: String(value), error: '0' })) }];
  });
}

// Reuse the first available name, including gaps left by removal or renaming.
export function defaultSampleName(rows, kind) {
  const used = new Set(rows.map(row => row.name));
  const letters = n => { let name = ''; do { name = String.fromCharCode(65 + n % 26) + name; n = Math.floor(n / 26) - 1; } while (n >= 0); return name; };
  for (let n = 0; ; n++) {
    const name = kind === 'point' ? letters(n) : 'ℓ' + String(n + 1).replace(/[0-9]/g, d => '₀₁₂₃₄₅₆₇₈₉'[Number(d)]);
    if (!used.has(name)) return name;
  }
}

export default function ConstructionPanel(props) {
  const rpc = useRpcSession(), editor = React.useContext(EditorContext);
  const [scene, setScene] = React.useState(null), sceneRef = React.useRef(null);
  const [operation, setOperation] = React.useState('1'), [inputs, setInputs] = React.useState([]);
  const [active, setActive] = React.useState(0), [viewport, setViewport] = React.useState(initialViewport);
  const [controlHelp, setControlHelp] = React.useState('');
  const [extraBits, setExtraBits] = React.useState(0), [busy, setBusy] = React.useState('');
  const [message, setMessage] = React.useState(''), [submission, setSubmission] = React.useState(null);
  const [finalPoint, setFinalPoint] = React.useState(1), [coordinate, setCoordinate] = React.useState('x');
  const [hover, setHover] = React.useState(null), [inspection, setInspection] = React.useState('');
  const [historyIndex, setHistoryIndex] = React.useState(null);
  const [previewValid, setPreviewValid] = React.useState(false);
  const [editingSamples, setEditingSamples] = React.useState(false);
  const [sampleRows, setSampleRows] = React.useState([]), [recipeName, setRecipeName] = React.useState('');
  const [placement, setPlacement] = React.useState(null), [tentative, setTentative] = React.useState(null);
  const [requirementFamily, setRequirementFamily] = React.useState('distinctPoints');
  const [requirementRefs, setRequirementRefs] = React.useState([]), [requirementValues, setRequirementValues] = React.useState(['x', '0']);
  const sampleDrag = React.useRef(null);
  const generation = React.useRef(0), drag = React.useRef(null), canvas = React.useRef(null);
  const gateKey = JSON.stringify(props.gate);
  const recipeOperations = (props.recipes ?? []).map(r => [r.id, `Recipe · ${r.name}`,
    r.parameters.map(p => p.name), r.parameters.map(p => p.kind),
    'Run this recipe on the selected inputs. Multiple folds will ask for a fresh choice.']);
  const availableOperations = [...operations, ...recipeOperations];
  const spec = availableOperations.find(o => o[0] === operation) ?? operations[0], box = bounds(viewport);
  const storedObjects = scene?.view.objects ?? [];
  const objects = editingSamples && (sampleRows.some(r => !r.keep) || tentative) ? samplePreview(sampleRows, storedObjects) : storedObjects;
  const choices = previewValid ? (scene?.view.choices ?? []) : [];
  const selectedGroup = typeof historyIndex === 'string' ? scene?.view.groups?.[Number(historyIndex.slice(7))] : null;
  const historyStep = selectedGroup ? { ...selectedGroup, description: selectedGroup.name } :
    scene?.view.history?.[historyIndex] ?? null;
  const objectLabel = index => `${(objects.find(o => o.index === index) ?? storedObjects.find(o => o.index === index))?.kind === 'point' ? 'P' : 'L'}${index}`;
  const bits = precisionFor(viewport.width, extraBits);
  function install(result) { sceneRef.current = result; setScene(result); setHistoryIndex(null); }
  async function request(action, overrides = {}) {
    const wasSetup = sceneRef.current?.workspace?.ready === false;
    const token = newGeneration(generation);
    setBusy(action === 'submit' ? (props.workspace ? 'Preparing recipe…' : 'Checking the complete proof…') : 'Computing…');
    setMessage(''); setSubmission(null);
    try {
      const response = await rpc.call('LeanOrigami.Widget.interact', {
        gate: props.gate, session: sceneRef.current?.session ?? null,
        action, operation, inputs: ['preview', 'intersect', 'recipe'].includes(action) ? inputs : [],
        choice: 0, point: finalPoint, coordinate, bits, recipeName: '', sampleInputs: [], requirement: { family: 'distinctPoints', references: [], values: [] }, ...overrides,
      });
      if (!isCurrent(generation, token)) return;
      install(response);
      if (['start', 'addRequirement', 'removeRequirement'].includes(action)) setRequirementRefs([]);
      if (response.workspace && ['start', 'samples', 'resetSamples'].includes(action)) {
        setSampleRows(response.workspace.inputs); setRecipeName(response.workspace.name);
        if (action === 'start') setEditingSamples(!response.workspace.ready);
        if (action === 'samples' && wasSetup) setEditingSamples(false);
        setPlacement(null); setTentative(null);
      }
      if (response.view.running || action === 'preview') setPreviewValid(true);
      else if (['start', 'choose', 'intersect', 'undo', 'recipe', 'samples', 'resetSamples', 'addRequirement', 'removeRequirement'].includes(action)) {
        setPreviewValid(false); setInputs([]); setActive(0); setHover(null); setInspection('');
        if (action === 'start') {
          setFinalPoint(response.point ?? 1); setCoordinate(response.coordinate ?? 'x');
          setViewport(initialViewport);
        }
        if (action === 'intersect') setFinalPoint(response.view.objects.at(-1).index);
        if (response.view.result != null && (props.workspace || response.view.objects.some(o =>
          o.index === response.view.result && o.kind === 'point'))) setFinalPoint(response.view.result);
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
    newGeneration(generation); setBusy(''); setSubmission(null); setMessage(''); setPreviewValid(false); setHistoryIndex(null);
    if (sceneRef.current) install({ ...sceneRef.current, view: { ...sceneRef.current.view, choices: [] } });
  }
  function select(index, kind) {
    if (busy || editingSamples || scene?.view.running) return;
    if (spec[3][active] !== kind) { setMessage(`Choose a ${spec[3][active]} for ${spec[2][active]}.`); return; }
    invalidate(); setInputs(old => { const next = [...old]; next[active] = index; return next; });
    setActive(Math.min(active + 1, spec[2].length - 1));
  }
  function screen([x, y]) {
    return [(x - box[0]) / viewport.width * WIDTH, HEIGHT - (y - box[2]) / viewport.width * WIDTH];
  }
  const workspace = scene?.workspace;
  const setup = props.workspace && workspace?.ready === false;
  function editRow(index, patch) {
    invalidate(); setSampleRows(rows => rows.map((r, i) => i === index ? { ...r, ...patch } : r));
  }
  function samplePosition(ev) {
    const rect = canvas.current.getBoundingClientRect();
    const x = box[0] + (ev.clientX - rect.left) / rect.width * viewport.width;
    const y = box[3] - (ev.clientY - rect.top) / rect.height * (box[3] - box[2]);
    return { exact: [snapSample(x, gridFor(viewport).step), snapSample(y, gridFor(viewport).step)], pixel: screen([x, y]) };
  }
  function placeSample(ev, index, first = null) {
    try {
      const position = samplePosition(ev), row = sampleRows[index];
      if (row.kind === 'line' && !first) { setPlacement({ index, first: position.exact }); return; }
      const values = row.kind === 'line' ? [...first, ...position.exact] : position.exact;
      const rows = sampleRows.map((r, i) => i === index ? { ...r, values, keep: false } : r);
      invalidate(); setSampleRows(rows); setPlacement(null); setTentative(null);
      if (!setup) request('samples', { sampleInputs: rows, recipeName });
    } catch (error) { setMessage(String(error)); }
  }
  function draw(object, candidate) {
    const values = visibleNumbers(object), selected = !candidate && inputs.includes(object.index);
    const historyRole = !candidate && historyStep ?
      (object.index === historyStep.output ? 'output' : historyStep.inputs.includes(object.index) ? 'input' : null) : null;
    const color = historyRole === 'output' || candidate ? '#e87925' :
      historyRole === 'input' || (!historyStep && selected) ? '#4ea1ff' : 'currentColor';
    const style = { cursor: 'pointer', opacity: historyStep && !historyRole ? 0.2 : 1 };
    const key = `${candidate ? 'c' : 'o'}${object.index}`;
    const title = `${candidate ? 'Choice' : object.kind} ${object.index + (candidate ? 1 : 0)}: ≈ ${describeObject(object)}`;
    const inspect = { onMouseEnter: () => { setInspection(title); if (candidate) setHover(object.index); },
      onMouseLeave: () => { setInspection(''); if (candidate) setHover(null); } };
    if (object.kind === 'point') {
      const [cx, cy] = screen(values);
      if (![cx, cy].every(Number.isFinite)) return null;
      return e('g', { key, ...inspect, 'data-history-role': historyRole,
        onPointerDown: ev => {
          if (!editingSamples || busy || placement || object.index >= sampleRows.length) return;
          ev.stopPropagation(); sampleDrag.current = object.index; canvas.current.setPointerCapture(ev.pointerId);
        }, onClick: () => select(object.index, 'point'), style },
        e('title', null, title), e('circle', { cx, cy, r: 12, fill: 'transparent' }),
        e('circle', { cx, cy, r: historyRole ? 6 : 4, fill: color }), e('text', { x: cx + 7, y: cy - 7, fill: color, fontSize: 12 }, `P${object.index}`));
    }
    const segment = clipLine(...values, box);
    if (!segment) return null;
    const [p, q] = segment.map(screen);
    // Anchor labels inside the clipped segment, then keep their text inside
    // the viewport even for horizontal/vertical lines at the canvas edge.
    const labelX = Math.max(6, Math.min(WIDTH - 60, p[0] * 0.8 + q[0] * 0.2 + 6));
    const labelY = Math.max(14, Math.min(HEIGHT - 6, p[1] * 0.8 + q[1] * 0.2 - 6));
    return e('g', { key, ...inspect, 'data-history-role': historyRole, onClick: () => candidate ? setHover(object.index) : select(object.index, 'line'), style },
      e('title', null, title), e('line', { x1: p[0], y1: p[1], x2: q[0], y2: q[1], stroke: 'transparent', strokeWidth: 12 }),
      e('line', { x1: p[0], y1: p[1], x2: q[0], y2: q[1], stroke: color,
        strokeWidth: historyRole ? 3.5 : candidate && hover === object.index ? 4 : 1.5, strokeDasharray: candidate ? '7 4' : undefined }),
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
  const requirementSpec = requirementFamilies.find(f => f[0] === requirementFamily);
  const combining = ['and', 'or', 'not'].includes(requirementFamily);
  const requirementFields = requirementFamily.startsWith('coordinate') || requirementFamily.startsWith('polynomial');
  const requirements = scene?.workspace?.requirements ?? [];
  const requirementLocked = !!busy || (!!scene?.view.running && !scene?.workspace?.replaying);
  const button = (label, onClick, disabled = false) => e('button', { type: 'button', onClick, disabled, style: { margin: '3px' } }, label);
  const helpButton = (label, onClick, help, disabled = false) => e('button', {
    onClick, disabled, title: help, 'aria-description': help,
    onFocus: () => setControlHelp(help), onBlur: () => setControlHelp(''),
    onMouseEnter: () => setControlHelp(help), onMouseLeave: () => setControlHelp(''),
    style: { marginRight: '5px' },
  }, label);

  function historyRow(step, i) {
    return e('li', {
      key: i, tabIndex: 0, onMouseMove: () => setHistoryIndex(i),
      onMouseLeave: () => setHistoryIndex(current => current === i ? null : current),
      onFocus: () => setHistoryIndex(i),
      onBlur: () => setHistoryIndex(current => current === i ? null : current),
      style: { padding: '4px', background: historyIndex === i ? 'var(--vscode-list-hoverBackground)' : undefined },
    }, `${step.description} → ${objectLabel(step.output)}`);
  }
  function historyRows(start = 0, end = scene?.view.history?.length ?? 0, excluded = []) {
    const history = scene?.view.history ?? [], groups = scene?.view.groups ?? [], rows = [];
    for (let i = start; i < end;) {
      const group = groups.filter(g => !excluded.includes(g) && g.start === i && g.count > 0 && i + g.count <= end)
        .sort((a, b) => b.count - a.count)[0];
      if (group) {
        const groupKey = `recipe:${groups.indexOf(group)}`;
        rows.push(e('li', { key: `group-${i}` }, e('details', null,
          e('summary', {
            onMouseMove: () => setHistoryIndex(groupKey), onFocus: () => setHistoryIndex(groupKey),
            onMouseLeave: () => setHistoryIndex(current => current === groupKey ? null : current),
            onBlur: () => setHistoryIndex(current => current === groupKey ? null : current),
          }, `${group.name} (${group.inputs.map(objectLabel).join(', ')}) → ${objectLabel(group.output)}`),
          e('ol', null, ...historyRows(i, i + group.count, [...excluded, group])))));
        i += group.count;
      } else { rows.push(historyRow(history[i], i)); i++; }
    }
    return rows;
  }
  const unresolvedDisplay = [...objects, ...choices].some(o => needsRefinement(o, viewport));
  return e('details', { open: true, style: { maxWidth: '760px' } },
    e('summary', null, 'Origami construction'),
    e('p', null, props.workspace ? `Recipe workspace: ${workspace?.name || props.target}` : `Goal: ${props.target}`),
    props.workspace && e('p', null, 'Sample inputs are parameters. Saving a recipe does not prove a theorem.'),
    props.workspace && e('p', null, (workspace?.inputs ?? props.parameters ?? []).map((p, i) => `${p.name}: ${p.kind === 'point' ? 'P' : 'L'}${i}`).join(' · ')),
    editingSamples && sampleRows.some(r => !r.keep) && e('p', { role: 'status' }, 'Sample edits are a draft. Apply them to recompute the construction.'),
    props.saved && e('p', null, props.workspace ? 'Saved recipe. Changes are drafts until you save them.' : 'Saved construction. Changes are drafts until you save them.'),
    e('svg', { ref: canvas, viewBox: `0 0 ${WIDTH} ${HEIGHT}`, role: 'img', 'aria-label': 'Origami construction canvas',
      style: { width: '100%', border: '1px solid currentColor', touchAction: 'none', background: 'var(--vscode-editor-background)' },
      onPointerDown: ev => { if (editingSamples && placement) { placeSample(ev, placement.index, placement.first); return; } if (ev.target === ev.currentTarget) { drag.current = { x: ev.clientX, y: ev.clientY, viewport }; ev.currentTarget.setPointerCapture(ev.pointerId); } },
      onPointerMove: ev => { if (sampleDrag.current !== null) { setTentative(samplePosition(ev).pixel); return; } if (drag.current) { const d = drag.current, scale = d.viewport.width / ev.currentTarget.getBoundingClientRect().width;
        setViewport({ ...d.viewport, x: d.viewport.x - (ev.clientX - d.x) * scale, y: d.viewport.y + (ev.clientY - d.y) * scale }); } },
      onPointerUp: ev => { if (sampleDrag.current !== null) { const index = sampleDrag.current; sampleDrag.current = null; placeSample(ev, index); } drag.current = null; }, onPointerCancel: () => { drag.current = null; sampleDrag.current = null; setTentative(null); },
    }, e('g', { pointerEvents: 'none', stroke: 'currentColor', fill: 'currentColor', strokeOpacity: 0.2, fillOpacity: 0.65, fontSize: 10 }, ...gridLines),
      ...objects.filter(o => o.kind === 'line' && o.index !== historyStep?.output).map(o => draw(o, false)),
      ...choices.map(o => draw(o, true)),
      ...objects.filter(o => o.kind === 'point' && o.index !== historyStep?.output).map(o => draw(o, false)),
      ...objects.filter(o => o.index === historyStep?.output).map(o => draw(o, false)),
      tentative && e('circle', { cx: tentative[0], cy: tentative[1], r: 7, fill: '#4ea1ff', pointerEvents: 'none' })),
    e('p', { role: 'status', style: { height: '4em', overflowY: 'auto', margin: '6px 0', fontSize: '0.9em' } },
      historyStep ? `${selectedGroup ? "Recipe" : `Step ${historyIndex + 1}`}: ${historyStep.description}. Inputs (blue): ${historyStep.inputs.map(objectLabel).join(', ')}. Output (orange): ${objectLabel(historyStep.output)}.` :
      inspection || 'Hover over a point or line to inspect its approximate coordinates or equation.'),
    e('details', { onToggle: ev => { if (!ev.currentTarget.open) setHistoryIndex(null); } },
      e('summary', null, 'Construction history'),
      e('p', null, 'Hover over a step or focus it with Tab to highlight its inputs and result.'),
      e('ol', { style: { maxHeight: '200px', overflowY: 'auto', margin: '6px 0' } }, ...historyRows(), scene?.view.failure && e('li', { 'aria-invalid': true, style: { color: 'var(--vscode-errorForeground)' } }, scene.view.failure))),
    e('div', null,
      button('Zoom in', () => setViewport(v => ({ ...v, width: Math.max(1e-12, v.width / 2) }))),
      button('Zoom out', () => setViewport(v => ({ ...v, width: Math.min(1e12, v.width * 2) }))),
      helpButton('Reset view', () => setViewport(initialViewport), 'Restore the initial camera position and zoom.'),
      helpButton('Refine display', () => setExtraBits(b => Math.min(480, b + 32)), 'Request more accurate drawing approximations. The exact construction and proof stay the same.', !!busy),
      button('Undo', () => request('undo'), !scene || scene.view.steps === 0 || !!scene.view.running || !!editingSamples)),
    controlHelp && e('p', { role: 'tooltip' }, controlHelp),
    unresolvedDisplay && e('p', { role: 'status' }, 'Some objects need more display precision. Refine or use the exact object list.'),
    props.workspace && e('section', { 'aria-label': 'Sample inputs' },
      !setup && button(editingSamples ? 'Finish editing samples' : 'Edit samples', () => {
        setEditingSamples(!editingSamples); setPlacement(null); setTentative(null); setSubmission(null);
      }, !!busy || (editingSamples && (sampleRows.some(r => !r.keep) || recipeName !== workspace?.name))),
      (setup || editingSamples) && e('fieldset', null, e('legend', null, setup ? 'Set up recipe' : 'Preview with different samples'),
        e('label', null, 'Recipe name ', e('input', { 'aria-label': 'Recipe name', placeholder: 'myMidpoint', value: recipeName, disabled: !!workspace?.nameLocked || !!busy,
          onChange: ev => { invalidate(); setRecipeName(ev.target.value); } })),
        e('p', null, 'Samples are inputs, not folding steps. Enter integers or fractions. Drag a sample point, or use Place for grid placement. Lines use two clicks. Exact replay runs on release.'),
        ...sampleRows.map((row, i) => e('fieldset', { key: i }, e('legend', null, `${row.kind} input ${i}`),
          e('label', null, 'Name ', e('input', { 'aria-label': `Input ${i} name`, value: row.name, disabled: !setup || !!busy,
            onChange: ev => editRow(i, { name: ev.target.value }) })),
          row.kind === 'line' && row.values.length !== 4 && e('p', null, 'Equation: a x + b y = c'),
          ...(row.kind === 'point' ? ['x', 'y'] : row.values.length === 4 ? ['x₁', 'y₁', 'x₂', 'y₂'] : ['a', 'b', 'c']).map((label, j) =>
            e('label', { key: j }, `${label} `, e('input', { 'aria-label': `Input ${i} ${label}`, value: row.values[j] ?? '',
              placeholder: 'unchanged exact value', disabled: !!busy, style: { width: '7em' },
              onChange: ev => { const values = [...row.values]; values[j] = ev.target.value; editRow(i, { values, keep: false }); } }))),
          row.keep && e('small', null, ' Exact input is preserved. Fill every coordinate to replace it.'),
          button(`Place ${row.name || row.kind}`, () => { setPlacement({ index: i, first: null }); setMessage(''); }, !!busy),
          row.kind === 'line' && button('Enter equation', () => editRow(i, { values: ['', '', ''], keep: false }), !!busy),
          setup && button(`Remove input ${i}`, () => { invalidate(); setSampleRows(rows => rows.filter((_, j) => j !== i)); setPlacement(null); }, !!busy))),
        setup && e('div', null, ...['point', 'line'].map(kind => button(`Add ${kind} input`, () => {
          invalidate(); setSampleRows(rows => [...rows, { name: defaultSampleName(rows, kind), kind, values: kind === 'point' ? ['0', '0'] : ['1', '0', '0'], keep: false }]);
        }, !!busy))),
        placement && e('p', { role: 'status' }, placement.first ? 'Click the second point of the sample line.' : 'Click on the canvas to place this input.'),
        button(setup ? 'Start construction' : 'Apply samples', () => request('samples', { sampleInputs: sampleRows, recipeName }), !!busy || !sampleRows.length),
        !setup && button('Reset samples', () => request('resetSamples'), !!busy))),
    props.workspace && !setup && e('details', { 'aria-label': 'Requirements' },
      e('summary', null, `Requirements (${requirements.length})`),
      e('p', null, 'Author-declared input requirements, checked exactly on the applied samples. These are not a proof of what the recipe achieves.'),
      e('ol', null, ...requirements.map((item, i) => e('li', { key: i },
        `${item.description} — ${item.status}`, button(`Remove requirement ${i + 1}`, () => request('removeRequirement', { choice: i }), requirementLocked)))),
      ...(scene?.workspace?.nestedRequirements ?? []).map((item, i) => e('p', { key: `nested-${i}` }, `From a nested recipe: ${item.description} — ${item.status}`)),
      e('label', null, 'Condition ', e('select', { 'aria-label': 'Requirement family', value: requirementFamily, disabled: requirementLocked,
        onChange: ev => { setRequirementFamily(ev.target.value); setRequirementRefs([]); setRequirementValues(['x', '0']); } },
        ...requirementFamilies.map(([value, label]) => e('option', { key: value, value }, label)))),
      ...requirementSpec[2].map((kind, i) => e('label', { key: `requirement-input-${i}` }, ` ${kind} ${i + 1} `,
        e('select', { 'aria-label': `Requirement input ${i + 1}`, value: requirementRefs[i] ?? '', disabled: requirementLocked,
          onChange: ev => setRequirementRefs(old => { const next = [...old]; next[i] = Number(ev.target.value); return next; }) },
          e('option', { value: '', disabled: true }, `Select ${kind}`),
          ...(kind === 'requirement' ? requirements.map((r, index) => ({ name: r.description, index })) :
            (workspace?.inputs ?? []).map((r, index) => ({ ...r, index })).filter(r => r.kind === kind))
            .map(r => e('option', { key: r.index, value: r.index }, r.name))))),
      requirementFields && e('div', null,
        e('label', null, 'Coordinate ', e('select', { 'aria-label': 'Requirement coordinate', value: requirementValues[0], disabled: requirementLocked,
          onChange: ev => setRequirementValues(old => [ev.target.value, old[1]]) }, e('option', { value: 'x' }, 'x'), e('option', { value: 'y' }, 'y'))),
        e('label', null, requirementFamily.startsWith('polynomial') ? ' Coefficients (constant first) ' : ' Value ',
          e('input', { 'aria-label': 'Requirement value', value: requirementValues[1], disabled: requirementLocked,
            onChange: ev => setRequirementValues(old => [old[0], ev.target.value]) })),
        e('small', null, requirementFamily.startsWith('polynomial') ? ' Integers or fractions, comma-separated. Example: −2, 0, 1 means t² − 2 (type - for minus).' : ' Use an integer or fraction. Use 0 to require a sign.')),
      combining && e('p', null, 'The selected requirements will be replaced by this combination; all remaining requirements must still hold.'),
      button(combining ? 'Combine requirements' : 'Add requirement', () => {
        request('addRequirement', { requirement: { family: requirementFamily, references: requirementRefs, values: requirementValues } });
        setRequirementRefs([]);
      }, requirementLocked || requirementSpec[2].some((_, i) => requirementRefs[i] === undefined))),
    scene?.view.failure && e('p', { role: 'alert' }, `${scene.view.failure} Downstream results are hidden. Edit samples or requirements, or reset samples to try again; the recipe is retained.`),
    !setup && !editingSamples && e('div', null,
    e('label', null, 'Operation ', e('select', { value: operation, disabled: !!busy || !!scene?.view.running, onChange: ev => { invalidate(); setOperation(ev.target.value); setInputs([]); setActive(0); } },
      ...availableOperations.map(o => e('option', { key: o[0], value: o[0] }, o[1])))),
    e('p', { style: { margin: '6px 0' } }, spec[4]),
    operation.startsWith('recipe:') && e('div', null, e('small', null, 'Author-declared requirements (checked before running):'),
      e('ul', null, ...((props.recipes ?? []).find(r => r.id === operation)?.requirements ?? []).map((text, i) => e('li', { key: i }, text)))),
    e('p', { style: { margin: '6px 0', fontSize: '0.9em' } },
      `Click a ${spec[3][active]} on the drawing for “${spec[2][active]}”, or use the dropdowns. Drag empty space to pan; scroll to zoom.`),
    ...spec[2].map((role, i) => e('label', { key: i, style: { display: 'block', margin: '5px 0' } }, `${role} `,
      e('select', { value: inputs[i] ?? '', disabled: !!busy || !!scene?.view.running, onFocus: () => setActive(i), onChange: ev => { invalidate(); setInputs(old => { const next = [...old]; next[i] = Number(ev.target.value); return next; }); } },
        e('option', { value: '', disabled: true }, `Select a ${spec[3][i]}`),
        ...objects.filter(o => o.kind === spec[3][i]).map(o => e('option', { key: o.index, value: o.index }, `${o.kind} ${o.index}`))))),
    button(operation.startsWith('recipe:') ? 'Run recipe' : operation === 'intersection' ? 'Add intersection' : 'Preview folds',
      () => request(operation.startsWith('recipe:') ? 'recipe' : operation === 'intersection' ? 'intersect' : 'preview'),
      !!busy || !!scene?.view.running || spec[2].some((_, i) => inputs[i] === undefined)),
    scene?.view.running && !scene.view.failure && e('p', null, workspace?.replaying ? 'Preview paused: choose a fold below, or edit/reset samples.' : 'Recipe paused: choose a fold below, or cancel the whole call.',
      !workspace?.replaying && button('Cancel recipe', () => request('undo'), !!busy))),
    choices.length > 0 && e('div', null, e('p', null, `${choices.length} exact choice(s). Select by number if previews overlap.`),
      ...choices.map(o => e('div', { key: o.index, onMouseEnter: () => setHover(o.index), onMouseLeave: () => setHover(null) },
        button(`Use fold ${o.index + 1}`, () => request('choose', { choice: o.index }), !!busy),
        e('small', null, describeObject(o))))),
    e('details', null, e('summary', null, `Objects · ${scene?.view.steps ?? 0} construction steps`),
      e('ul', null, ...objects.map(o => e('li', { key: o.index },
        button(`${o.kind} ${o.index}`, () => select(o.index, o.kind)),
        e('span', null, describeObject(o)))))),
    !setup && !editingSamples && e('fieldset', null, e('legend', null, props.workspace ? 'Recipe output' : 'Submit a coordinate'),
      e('select', { 'aria-label': props.workspace ? 'Recipe output' : 'Final point', disabled: !!busy || !!scene?.view.running, value: objects.some(o => (props.workspace || o.kind === 'point') && o.index === finalPoint) ? finalPoint : '', onChange: ev => { invalidate(); setFinalPoint(Number(ev.target.value)); } },
        e('option', { value: '', disabled: true }, props.workspace ? 'Select an object' : 'Select a point'),
        ...objects.filter(o => props.workspace || o.kind === 'point').map(o => e('option', { key: o.index, value: o.index }, `${o.kind} ${o.index}`))),
      !props.workspace && e('select', { 'aria-label': 'Coordinate', disabled: !!busy || !!scene?.view.running, value: coordinate, onChange: ev => { invalidate(); setCoordinate(ev.target.value); } },
        e('option', { value: 'x' }, 'x coordinate'), e('option', { value: 'y' }, 'y coordinate')),
      button(props.workspace ? 'Prepare recipe' : 'Submit', () => request('submit'), !!busy || !!scene?.view.running || !scene || !objects.some(o => (props.workspace || o.kind === 'point') && o.index === finalPoint))),
    busy && e('p', { role: 'status' }, busy), message && e('p', { role: 'alert' }, message),
    submission && e('div', null, e('p', null, props.workspace ? 'Recipe references and input kinds checked. This is a reusable construction, not a theorem about its output.' : 'Lean checked this proof against the original goal.'),
      button(props.workspace ? 'Save recipe' : 'Save construction', async () => { try {
        await editor.api.applyEdit({ documentChanges: [submission.edit] });
        setSubmission(null);
      } catch (err) { setMessage(`The source changed or saving failed: ${String(err)}`); } }),
      e('details', null, e('summary', null, 'Saved construction source'), e('pre', { style: { overflow: 'auto', maxHeight: '240px' } }, submission.source))));
}
