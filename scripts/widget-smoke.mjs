// Exercise the pinned ProofWidgets click handler against a minimal editor
// adapter. This is an integration harness, not a claim of visual GUI testing.
import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import vm from 'node:vm';

const props = JSON.parse(await fs.readFile('.lake/phase0/widget-edit.json', 'utf8'));
const source = 'example : (1 : Nat) + 1 = 2 := by\n  origami_phase0\n';
let text = source;
let version = 7;
let revealCount = 0;
let editCount = 0;
const context = vm.createContext({ window: {} });
const editor = {
  api: {
    async applyEdit({ documentChanges }) {
      assert.equal(documentChanges.length, 1);
      const edit = documentChanges[0];
      assert.equal(edit.textDocument.uri, 'file:///phase0/WidgetReplay.lean');
      if (edit.textDocument.version !== version) throw new Error('stale document');
      assert.equal(edit.edits.length, 1);
      const { range, newText } = edit.edits[0];
      const lines = text.split('\n');
      assert.equal(range.start.line, range.end.line);
      const line = lines[range.start.line];
      assert.equal(line.slice(range.start.character, range.end.character), 'origami_phase0');
      lines[range.start.line] = line.slice(0, range.start.character) + newText +
        line.slice(range.end.character);
      text = lines.join('\n');
      version++;
      editCount++;
    },
  },
  async revealLocation({ range }) {
    assert.deepEqual(range.start, { line: 1, character: 5 });
    revealCount++;
  },
};
const exportsByModule = {
  'react': { useContext: () => editor },
  'react/jsx-runtime': { jsx: (tag, properties) => ({ tag, properties }) },
  '@leanprover/infoview': { EditorContext: {} },
};
const code = await fs.readFile(
  '.lake/packages/proofwidgets/widget/js/makeEditLink.js', 'utf8');
const module = new vm.SourceTextModule(code, { context });
await module.link(async specifier => {
  const exports = exportsByModule[specifier];
  assert.ok(exports, `unexpected dependency: ${specifier}`);
  return new vm.SyntheticModule(Object.keys(exports), function () {
    for (const [name, value] of Object.entries(exports)) this.setExport(name, value);
  }, { context });
});
await module.evaluate();
const link = module.namespace.default({ ...props, children: 'Insert checked proof' });
assert.equal(link.tag, 'a');
await link.properties.onClick();
assert.equal(text, 'example : (1 : Nat) + 1 = 2 := by\n  rfl\n');
assert.equal(editCount, 1);
assert.equal(revealCount, 1);
await assert.rejects(link.properties.onClick(), /stale document/);
assert.equal(editCount, 1);
await fs.writeFile('.lake/phase0/WidgetReplay.lean', text);
console.log('PASS: pinned widget click applies the Lean-generated versioned edit');
console.log('PASS: stale edit rejected by editor adapter; replay file written');
