// CodeMirror setups: the TypeScript editor and the Lean viewers, with hovers, lenses and folds.
import { EditorState, StateEffect, StateField, RangeSetBuilder, type Extension, Compartment } from "@codemirror/state";
import {
  EditorView, keymap, lineNumbers, highlightActiveLine, highlightActiveLineGutter, drawSelection,
  hoverTooltip, Decoration, WidgetType, type DecorationSet,
} from "@codemirror/view";
import { defaultKeymap, history, historyKeymap, indentWithTab } from "@codemirror/commands";
import {
  syntaxHighlighting, HighlightStyle, StreamLanguage, bracketMatching, indentOnInput, codeFolding,
  foldEffect, unfoldEffect, foldedRanges, foldGutter, type StreamParser,
} from "@codemirror/language";
import { javascript } from "@codemirror/lang-javascript";
import { closeBrackets, closeBracketsKeymap } from "@codemirror/autocomplete";
import { searchKeymap, highlightSelectionMatches } from "@codemirror/search";
import { lintGutter } from "@codemirror/lint";
import { tags as t } from "@lezer/highlight";
import { h, icon } from "./util";

/* ── Theme ──────────────────────────────────────────────────────────────── */

const theme = EditorView.theme({
  "&": { color: "var(--text)", backgroundColor: "var(--surface)", fontSize: "13px", height: "100%" },
  ".cm-scroller": { fontFamily: "var(--font-code)", lineHeight: "1.6", overflow: "auto", fontVariantLigatures: "none" },
  ".cm-content": { caretColor: "var(--thread)", padding: "10px 0 40vh" },
  ".cm-cursor, .cm-dropCursor": { borderLeftColor: "var(--thread)", borderLeftWidth: "2px" },
  "&.cm-focused .cm-selectionBackground, .cm-selectionBackground, .cm-content ::selection": { backgroundColor: "var(--sel) !important" },
  ".cm-gutters": { backgroundColor: "var(--surface)", color: "var(--muted)", border: "none", paddingRight: "4px" },
  ".cm-lineNumbers .cm-gutterElement": { padding: "0 8px 0 14px", minWidth: "44px", opacity: ".7", fontSize: "11.5px" },
  ".cm-activeLine": { backgroundColor: "var(--active-line)" },
  ".cm-activeLineGutter": { backgroundColor: "transparent", color: "var(--text)" },
  ".cm-line": { padding: "0 14px 0 6px" },
  ".cm-matchingBracket": { backgroundColor: "var(--surface-3)", outline: "1px solid var(--border-strong)" },
  ".cm-selectionMatch": { backgroundColor: "var(--thread-soft)" },
  ".cm-foldGutter .cm-gutterElement": { color: "var(--muted)", opacity: ".5", cursor: "pointer" },
  ".cm-foldGutter .cm-gutterElement:hover": { opacity: "1" },
  ".cm-tooltip": { color: "var(--text)" },
  ".cm-diagnostic": { fontFamily: "var(--font-ui)", fontSize: "12.5px", padding: "6px 10px" },
  ".cm-diagnostic-error": { borderLeftColor: "var(--err)" },
  ".cm-lintRange-error": {
    backgroundImage: "none", textDecoration: "underline wavy var(--err)", textUnderlineOffset: "3px", textDecorationSkipInk: "none",
  },
  ".cm-lint-marker-error": { content: "none" },
  ".cm-panels": { backgroundColor: "var(--surface-2)", color: "var(--text)" },
  ".cm-searchMatch": { backgroundColor: "var(--warn-soft)", outline: "1px solid var(--warn)" },
  ".cm-hover-target": { backgroundColor: "var(--thread-soft)", borderRadius: "3px" },
  ".cm-tactic": { backgroundColor: "var(--info-soft)", borderRadius: "3px", boxShadow: "0 0 0 1px var(--info-soft)" },
  ".cm-flash-line": { animation: "flash 2.2s ease-out" },
});

const highlight = HighlightStyle.define([
  { tag: [t.keyword, t.controlKeyword, t.moduleKeyword, t.definitionKeyword, t.operatorKeyword, t.modifier], color: "var(--syn-keyword)" },
  { tag: [t.typeName, t.className, t.namespace], color: "var(--syn-type)" },
  { tag: [t.string, t.special(t.string), t.character, t.regexp], color: "var(--syn-string)" },
  { tag: [t.number, t.bool, t.null, t.atom], color: "var(--syn-number)" },
  { tag: [t.comment, t.lineComment, t.blockComment], color: "var(--syn-comment)", fontStyle: "italic" },
  { tag: t.docComment, color: "var(--syn-comment)" },
  { tag: [t.function(t.definition(t.variableName)), t.definition(t.variableName), t.function(t.variableName), t.definition(t.propertyName)], color: "var(--syn-def)" },
  { tag: [t.operator, t.punctuation, t.separator, t.bracket], color: "var(--syn-op)" },
  { tag: [t.meta, t.annotation, t.macroName], color: "var(--syn-meta)" },
  { tag: [t.variableName, t.propertyName], color: "var(--syn-ident)" },
]);

/* ── Lean ───────────────────────────────────────────────────────────────── */

const leanKeywords = new Set(("def theorem lemma abbrev structure inductive instance class where with match fun let have show " +
  "from by at in if then else do return namespace end open section variable import set_option noncomputable private " +
  "protected partial unsafe mutual deriving example calc termination_by decreasing_by universe macro syntax elab " +
  "attribute local scoped public meta module export axiom opaque").split(" "));
const leanTactics = new Set(("intro intros exact refine apply simp simp_all simp_only omega decide rfl unfold split rename_i " +
  "rcases obtain rintro cases induction constructor contradiction subst revert generalize dsimp rw rwa assumption " +
  "exists use left right trivial calc show by_cases by_contra false_or_by_contra repeat first all_goals any_goals " +
  "try skip next case funext ext congr specialize suffices change norm_num linarith positivity aesop simpa " +
  "kernel_rfl cmp_laws ariadne_safe native_decide exfalso nofun").split(" "));

interface LeanState { comment: number; afterDef: boolean }
/** The rest of a (nested) block comment on this line. */
function blockComment(stream: Parameters<StreamParser<LeanState>["token"]>[0], state: LeanState) {
  while (!stream.eol()) {
    if (stream.match("/-")) state.comment++;
    else if (stream.match("-/")) { state.comment--; if (state.comment === 0) break; }
    else stream.next();
  }
  return "comment";
}
const leanParser: StreamParser<LeanState> = {
  name: "lean",
  startState: () => ({ comment: 0, afterDef: false }),
  token(stream, state) {
    if (state.comment > 0) return blockComment(stream, state);
    if (stream.eatSpace()) return null;
    if (stream.match("--")) { stream.skipToEnd(); return "lineComment"; }
    if (stream.match(/^\/-[-!]?/)) { state.comment = 1; return blockComment(stream, state); }
    if (stream.match(/^"(?:[^"\\]|\\.)*"?/)) return "string";
    if (stream.match(/^'(?:[^'\\]|\\.)'/)) return "string";
    if (stream.match(/^@\[[^\]]*\]/)) return "meta";
    if (stream.match(/^\d+(\.\d+)?/)) return "number";
    if (stream.match(/^[⊢→←↔∀∃λ≤≥≠∧∨¬×⊕∘▸⟨⟩∣∈∉⊆]/)) return "operator";
    const ident = stream.match(/^(?:«[^»]*»|[A-Za-z_Ͱ-Ͽᴀ-ᶿ][\w'!?Ͱ-Ͽ₀-₉]*)(?:\.(?:«[^»]*»|[A-Za-z_][\w'!?₀-₉]*))*/) as RegExpMatchArray | null;
    if (ident) {
      const word = ident[0];
      if (state.afterDef) { state.afterDef = false; return "definition"; }
      if (leanKeywords.has(word)) {
        if (/^(def|theorem|lemma|abbrev|structure|inductive|instance|class|axiom|opaque)$/.test(word)) state.afterDef = true;
        return "keyword";
      }
      if (leanTactics.has(word)) return "macroName";
      if (/^(true|false|True|False)$/.test(word)) return "atom";
      if (/^[A-Z]/.test(word) && !word.includes("«")) return "typeName";
      return "variableName";
    }
    if (stream.match(/^[:=<>+\-*\/|&!^%$#?~.,;()[\]{}]+/)) return "operator";
    stream.next();
    return null;
  },
  languageData: { commentTokens: { line: "--", block: { open: "/-", close: "-/" } } },
  tokenTable: { definition: t.definition(t.variableName), macroName: t.macroName, lineComment: t.lineComment },
};
const lean = StreamLanguage.define(leanParser);

/* ── Hovers ─────────────────────────────────────────────────────────────── */

/** Hover content at a position: the DOM to show, and the range it describes. */
export type HoverProvider = (pos: number) => { from: number; to: number; dom: HTMLElement } | null;

function hovers(provider: () => HoverProvider | null): Extension {
  return hoverTooltip((view, pos) => {
    const found = provider()?.(pos);
    if (!found) return null;
    return { pos: found.from, end: found.to, above: true, create: () => ({ dom: found.dom }) };
  }, { hoverTime: 220 });
}

/* ── Decorations set from outside: lenses, the current tactic ───────────── */

export interface Lens { pos: number; dom: () => HTMLElement }
const setLenses = StateEffect.define<Lens[]>();
class LensWidget extends WidgetType {
  constructor(readonly lens: Lens, readonly key: string) { super(); }
  eq(other: LensWidget) { return other.key === this.key; }
  toDOM() { return this.lens.dom(); }
  ignoreEvent() { return true; }
}
const lensField = StateField.define<DecorationSet>({
  create: () => Decoration.none,
  update(deco, tr) {
    deco = deco.map(tr.changes);
    for (const e of tr.effects) {
      if (e.is(setLenses)) {
        const b = new RangeSetBuilder<Decoration>();
        for (const lens of [...e.value].sort((a, b) => a.pos - b.pos)) {
          if (lens.pos > tr.state.doc.length) continue;
          const line = tr.state.doc.lineAt(lens.pos);
          b.add(line.from, line.from, Decoration.widget({ widget: new LensWidget(lens, `${line.number}:${lens.dom().textContent}`), block: true, side: -1 }));
        }
        deco = b.finish();
      }
    }
    return deco;
  },
  provide: (f) => EditorView.decorations.from(f),
});

const setMark = StateEffect.define<{ from: number; to: number; cls: string } | null>();
const markField = StateField.define<DecorationSet>({
  create: () => Decoration.none,
  update(deco, tr) {
    deco = deco.map(tr.changes);
    for (const e of tr.effects) {
      if (e.is(setMark)) {
        deco = e.value && e.value.to > e.value.from
          ? Decoration.set([Decoration.mark({ class: e.value.cls }).range(e.value.from, e.value.to)])
          : Decoration.none;
      }
    }
    return deco;
  },
  provide: (f) => EditorView.decorations.from(f),
});

/* ── Folding the kernel-checked machinery of a generated file ───────────── */

interface Fold { from: number; to: number; label: string; lines: number }

/** The parts of a generated file a reader skips: the syntax tree, typed syntax, per-file checks and
the denotation equations. They are what the kernel checks; the readable definitions, safety conditions
and theorems stay visible. */
export function machinery(text: string): Fold[] {
  const lines = text.split("\n");
  const offsets: number[] = [];
  let o = 0;
  for (const l of lines) { offsets.push(o); o += l.length + 1; }
  const top = /^(\/-[-!]|noncomputable|def |theorem |abbrev |@\[|set_option|namespace|end |open |import |-- |instance )/;
  // Top-level blocks, each with its leading doc comment.
  const blocks: { start: number; end: number; name: string; header: string }[] = [];
  let i = 0;
  while (i < lines.length) {
    if (!top.test(lines[i])) { i++; continue; }
    const start = i;
    let header = lines[i];
    if (lines[i].startsWith("/-")) {
      while (i < lines.length && !lines[i].includes("-/")) i++;
      i++;
      if (lines[start].startsWith("/-!")) { blocks.push({ start, end: i, name: "/-!", header: lines[start] }); continue; }
      header = lines[i] ?? "";
    }
    i++;
    while (i < lines.length && !top.test(lines[i])) i++;
    let end = i;
    while (end > start + 1 && lines[end - 1].trim() === "") end--;
    const name = header.match(/(?:def|theorem|abbrev|instance)\s+(\S+)/)?.[1] ?? header.split(/\s/)[0];
    blocks.push({ start, end, name, header });
  }
  const category = (b: { name: string; header: string }): string | null => {
    const n = b.name;
    if (b.name === "/-!") return /## (Denotation|Frames)/.test(b.header) ? "section" : null;
    if (b.header.startsWith("set_option")) return "options";
    if (n === "ast") return "syntax tree";
    if (/^ty\./.test(n)) return "types";
    if (/^sig\.|^sigs$/.test(n)) return "signatures";
    if (/^ne\./.test(n)) return "name lemmas";
    if (/^body\.|^typed$/.test(n)) return "typed syntax";
    if (/^(erased|bodies_ok|ast_scoped|wf)$/.test(n)) return "per-file checks";
    if (/\.(uncurried|safety|body_eq|safe_eq)$/.test(n) || /^(denote_eq|safety_eq)$/.test(n)) return "denotation equations";
    if (/^frames\./.test(n)) return "frame checks";
    return null;
  };
  const folds: Fold[] = [];
  let group: { start: number; end: number; cats: Set<string> } | null = null;
  const flush = () => {
    if (!group) return;
    const cats = [...group.cats].filter((c) => c !== "section" && c !== "options");
    if (cats.length > 0 || group.end - group.start > 2) {
      const from = offsets[group.start];
      const to = offsets[group.end - 1] + lines[group.end - 1].length;
      folds.push({ from, to, lines: group.end - group.start, label: cats.join(", ") || "options" });
    }
    group = null;
  };
  for (let k = 0; k < blocks.length; k++) {
    const b = blocks[k];
    const cat = category(b);
    if (cat) {
      // Blank lines between hidden blocks join the group.
      if (group && blocks[k - 1] && lines.slice(group.end, b.start).every((l) => l.trim() === "")) {
        group.end = b.end;
        group.cats.add(cat);
      } else {
        flush();
        group = { start: b.start, end: b.end, cats: new Set([cat]) };
      }
    } else flush();
  }
  flush();
  return folds;
}

function machineryPlaceholder(fold: Fold | undefined, onclick: (e: Event) => void) {
  const label = fold ? `${fold.lines} lines: ${fold.label}` : "folded";
  return h("span", { class: "cm-machinery", onclick, title: "Checked by Lean's kernel when the file builds. Click to show." },
    icon("layers"), label);
}

/* ── Editors ────────────────────────────────────────────────────────────── */

const readOnly = [EditorState.readOnly.of(true), EditorView.editable.of(true)];

export class CodeView {
  view: EditorView;
  hoverProvider: HoverProvider | null = null;
  private folds: Fold[] = [];
  private wrap = new Compartment();

  constructor(parent: HTMLElement, opts: {
    doc: string; language: "ts" | "lean"; editable?: boolean; onChange?: (text: string) => void;
    onCursor?: (pos: number) => void; fold?: boolean; lint?: Extension; wrap?: boolean;
  }) {
    const ext: Extension[] = [
      theme, syntaxHighlighting(highlight), lineNumbers(), highlightActiveLineGutter(), highlightActiveLine(),
      drawSelection(), bracketMatching(), highlightSelectionMatches(), this.wrap.of(opts.wrap === false ? [] : EditorView.lineWrapping),
      keymap.of([...defaultKeymap, ...searchKeymap]),
      opts.language === "ts" ? javascript({ typescript: true }) : lean,
      hovers(() => this.hoverProvider), lensField, markField,
      EditorView.contentAttributes.of({ "aria-label": opts.language === "ts" ? "TypeScript source" : "Lean" }),
    ];
    if (opts.editable) {
      ext.push(history(), indentOnInput(), closeBrackets(), keymap.of([...closeBracketsKeymap, ...historyKeymap, indentWithTab]));
    } else ext.push(...readOnly);
    if (opts.lint) ext.push(opts.lint, lintGutter());
    if (opts.fold) {
      ext.push(codeFolding({
        preparePlaceholder: (_state, range) => this.folds.find((f) => f.from === range.from),
        placeholderDOM: (_view, onclick, prepared) => machineryPlaceholder(prepared as Fold | undefined, onclick),
      }), foldGutter({ markerDOM: (open) => {
        const s = icon("chevron");
        s.style.width = "12px";
        if (!open) s.style.transform = "rotate(-90deg)";
        return h("span", null, s);
      } }));
    }
    if (opts.onChange) {
      ext.push(EditorView.updateListener.of((u) => { if (u.docChanged) opts.onChange!(u.state.doc.toString()); }));
    }
    if (opts.onCursor) {
      ext.push(EditorView.updateListener.of((u) => {
        if (u.selectionSet || u.docChanged) opts.onCursor!(u.state.selection.main.head);
      }));
    }
    this.view = new EditorView({ parent, state: EditorState.create({ doc: opts.doc, extensions: ext }) });
  }

  get text() { return this.view.state.doc.toString(); }

  setText(text: string, foldMachinery = false) {
    const effects: StateEffect<unknown>[] = [];
    this.folds = foldMachinery ? machinery(text) : [];
    this.view.dispatch({ changes: { from: 0, to: this.view.state.doc.length, insert: text }, selection: { anchor: 0 }, scrollIntoView: true });
    if (foldMachinery) for (const f of this.folds) effects.push(foldEffect.of({ from: f.from, to: f.to }));
    if (effects.length) this.view.dispatch({ effects });
  }

  /** Fold or unfold every machinery block. */
  setMachineryFolded(folded: boolean) {
    if (folded) {
      this.view.dispatch({ effects: this.folds.map((f) => foldEffect.of({ from: f.from, to: f.to })) });
    } else {
      const effects: StateEffect<unknown>[] = [];
      foldedRanges(this.view.state).between(0, this.view.state.doc.length, (from, to) => { effects.push(unfoldEffect.of({ from, to })); });
      this.view.dispatch({ effects });
    }
  }

  get machineryLines() { return this.folds.reduce((n, f) => n + f.lines, 0); }

  setLenses(lenses: Lens[]) { this.view.dispatch({ effects: setLenses.of(lenses) }); }

  mark(range: { from: number; to: number } | null, cls = "cm-tactic") {
    this.view.dispatch({ effects: setMark.of(range ? { ...range, cls } : null) });
  }

  setWrap(on: boolean) { this.view.dispatch({ effects: this.wrap.reconfigure(on ? EditorView.lineWrapping : []) }); }

  reveal(pos: number, select = false) {
    this.view.dispatch({
      selection: select ? { anchor: pos } : undefined,
      effects: EditorView.scrollIntoView(pos, { y: "start", yMargin: 60 }),
    });
  }

  replace(from: number, to: number, insert: string) {
    this.view.dispatch({ changes: { from, to, insert }, selection: { anchor: from + insert.length } });
    this.view.focus();
  }
}

