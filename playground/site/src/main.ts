import "./styles.css";
import { setDiagnostics } from "@codemirror/lint";
import { CodeView, type Lens, type HoverProvider } from "./editors";
import { explain } from "./diagnostics";
import { LeanView, ProofsView } from "./lean";
import { RunView, type Presets } from "./run";
import { SubsetView } from "./subset";
import { translator, Timeout } from "./workers";
import type { BuildInfo, ExampleData, ExampleMeta, Hover, Translation } from "./types";
import { byteMapper, copyText, debounce, fill, h, icon, storage, toast } from "./util";

const REPO = "https://github.com/nathsou/ariadne";
const BLANK = `// Write TypeScript in the subset: Ariadne translates it as you type.
// Hover a name to see what it denotes in Lean.

export type Shape =
  | { kind: "circle"; r: number }
  | { kind: "rect"; w: number; h: number };

/** The area, in whole units (numbers are integers in the subset). */
export function area(s: Shape): number {
  switch (s.kind) {
    case "circle":
      return Math.floor((314 * s.r * s.r) / 100);
    case "rect":
      return s.w * s.h;
  }
}

/** The sum of the areas. */
export function total(shapes: readonly Shape[]): number {
  let sum = 0;
  for (const s of shapes) {
    sum += area(s);
  }
  return sum;
}
`;

/* ── State ──────────────────────────────────────────────────────────────── */

let examples: ExampleMeta[] = [];
let build: BuildInfo = { version: "", commit: "", lean: "" };
let current: ExampleData | null = null;
let original = "";
let lastGood: (Translation & { ok: true }) | null = null;
let tab = storage.get("ariadne-tab") ?? "lean";
const cache = new Map<string, Promise<ExampleData>>();

const loadExample = (slug: string) => {
  if (!cache.has(slug)) cache.set(slug, fetch(`data/${slug}.json`).then((r) => {
    if (!r.ok) throw new Error(`no example '${slug}'`);
    return r.json();
  }));
  return cache.get(slug)!;
};

/* ── Layout ─────────────────────────────────────────────────────────────── */

const app = document.getElementById("app")!;
const fileName = h("span", { class: "file-name" }, h("span", { class: "lang-badge ts" }, "TS"), h("span", { class: "name" }), h("span", { class: "dot", title: "Edited" }));
const status = h("span", { class: "status", role: "status", "aria-live": "polite" });
const resetBtn = h("button", { class: "btn small ghost", hidden: true, title: "Restore the example", onclick: () => restore() }, icon("reset"), "Restore");
const tsHost = h("div", { class: "editor-host" });
const dock = h("div", { class: "diag-dock" });
const introSlot = h("div");

const exampleBtn = h("button", { class: "btn example-btn", "aria-haspopup": "dialog", onclick: (e: Event) => { e.stopPropagation(); openGallery(); } },
  icon("book"), h("span", { class: "title" }, "Examples"), h("span", { class: "chev" }, icon("chevron")));
const themeBtn = h("button", { class: "btn icon ghost", title: "Toggle theme", "aria-label": "Toggle theme", onclick: () => toggleTheme() });

const tabsEl = h("div", { class: "tabs", role: "tablist" });
const viewsEl = h("div", { class: "pane-body" });

const leanView = new LeanView();
const leanEmpty = h("div", { class: "empty-state", style: "position:absolute;inset:0;background:var(--surface);z-index:3" },
  icon("lean"), h("h3", null, "Nothing translated yet"),
  h("p", null, "The program on the left is outside the subset. The explanation under the editor says why, and how to rewrite it."));
leanView.el.append(leanEmpty);
const proofsView = new ProofsView();
const runView = new RunView();
const guardsHost = h("div", { class: "editor-host" });
const guardsView = h("div", { class: "view" },
  h("div", { class: "banner info" }, icon("shield"), h("span", { class: "grow" },
    h("b", null, "Boundary guards. "), "A source theorem assumes its arguments represent the declared types: safe integers, records with their fields, arrays without holes. Inside the subset that holds by typing; where values come from outside (storage, the network), check it with these generated guards: ",
    h("code", null, "if (!args.f(x)) throw …"), ". The Run tab uses them too.")),
  guardsHost);
const subsetView = new SubsetView(() => fetch("data/LANGUAGE.md").then((r) => r.text()));

const views: Record<string, { label: string; el: HTMLElement; icon: string }> = {
  lean: { label: "Lean", el: leanView.el, icon: "lean" },
  proofs: { label: "Proofs", el: proofsView.el, icon: "shield" },
  run: { label: "Run", el: runView.el, icon: "play" },
  guards: { label: "Guards", el: guardsView, icon: "check" },
  subset: { label: "Subset", el: subsetView.el, icon: "book" },
};
const tabButtons = new Map<string, HTMLElement>();
for (const [key, v] of Object.entries(views)) {
  const b = h("button", { class: "tab", role: "tab", "aria-selected": "false", onclick: () => selectTab(key) }, icon(v.icon), v.label);
  tabButtons.set(key, b);
  tabsEl.append(b);
  v.el.hidden = true;
  viewsEl.append(v.el);
}

const workspace = h("main", { class: "workspace", "data-show": "left" },
  h("section", { class: "pane left", "aria-label": "TypeScript" },
    h("div", { class: "pane-head" }, fileName, h("span", { class: "spacer" }), status, resetBtn),
    introSlot, tsHost, dock),
  h("div", { class: "divider", role: "separator", "aria-orientation": "vertical", "aria-label": "Resize" }),
  h("section", { class: "pane right", "aria-label": "Output" },
    h("div", { class: "pane-head" }, tabsEl), viewsEl));

const mobileSeg = h("div", { class: "seg", role: "tablist" },
  h("button", { "aria-pressed": "true", onclick: () => showPane("left") }, "TypeScript"),
  h("button", { "aria-pressed": "false", onclick: () => showPane("right") }, "Lean & proofs"));

const footer = h("footer", { class: "footer" });

fill(app, 
  h("header", { class: "topbar" },
    h("a", { class: "brand", href: "./", title: "Ariadne playground" },
      (() => { const s = document.createElementNS("http://www.w3.org/2000/svg", "svg"); s.setAttribute("viewBox", "0 0 32 32"); s.innerHTML = '<use href="#mark"/>'; return s; })(),
      h("span", { class: "brand-name" }, "Ariadne"), h("span", { class: "brand-sub" }, "playground")),
    h("span", { class: "version" }),
    exampleBtn, h("span", { class: "spacer" }),
    h("button", { class: "btn", onclick: () => share() }, icon("share"), h("span", { class: "hide-narrow" }, "Share")),
    h("a", { class: "btn ghost hide-narrow", href: `${REPO}/blob/main/docs/GUIDE.md`, target: "_blank", rel: "noopener" }, icon("book"), "Guide"),
    h("a", { class: "btn icon ghost", href: REPO, target: "_blank", rel: "noopener", title: "GitHub", "aria-label": "GitHub" }, icon("github")),
    themeBtn),
  h("div", { class: "mobile-switch" }, mobileSeg),
  workspace, footer);

function showPane(which: "left" | "right") {
  workspace.dataset.show = which;
  const [a, b] = mobileSeg.children;
  a.setAttribute("aria-pressed", String(which === "left"));
  b.setAttribute("aria-pressed", String(which === "right"));
}

function selectTab(key: string) {
  tab = key;
  storage.set("ariadne-tab", key);
  for (const [k, b] of tabButtons) b.setAttribute("aria-selected", String(k === key));
  for (const [k, v] of Object.entries(views)) v.el.hidden = k !== key;
  if (key === "subset") void subsetView.ensure();
}

/* ── Divider ────────────────────────────────────────────────────────────── */

{
  const divider = workspace.querySelector(".divider") as HTMLElement;
  const left = workspace.querySelector(".pane.left") as HTMLElement;
  const saved = storage.get("ariadne-split");
  if (saved) left.style.setProperty("--split", saved);
  divider.addEventListener("pointerdown", (e) => {
    divider.setPointerCapture(e.pointerId);
    divider.classList.add("dragging");
    const box = workspace.getBoundingClientRect();
    const move = (m: PointerEvent) => {
      const pct = Math.min(75, Math.max(22, ((m.clientX - box.left) / box.width) * 100));
      left.style.setProperty("--split", `${pct}%`);
    };
    const up = () => {
      divider.classList.remove("dragging");
      storage.set("ariadne-split", left.style.getPropertyValue("--split"));
      divider.removeEventListener("pointermove", move);
      divider.removeEventListener("pointerup", up);
    };
    divider.addEventListener("pointermove", move);
    divider.addEventListener("pointerup", up);
  });
}

/* ── Theme ──────────────────────────────────────────────────────────────── */

function isDark() {
  const t = document.documentElement.dataset.theme;
  return t ? t === "dark" : matchMedia("(prefers-color-scheme: dark)").matches;
}
function renderThemeButton() { fill(themeBtn, icon(isDark() ? "sun" : "moon")); }
function toggleTheme() {
  const next = isDark() ? "light" : "dark";
  document.documentElement.dataset.theme = next;
  storage.set("ariadne-theme", next);
  renderThemeButton();
}
renderThemeButton();

/* ── The TypeScript editor ──────────────────────────────────────────────── */

const ts = new CodeView(tsHost, { doc: "", language: "ts", editable: true, lint: [], onChange: () => onEdit() });
const guards = new CodeView(guardsHost, { doc: "", language: "ts" });

const onEdit = () => {
  const text = ts.text;
  const modified = current !== null && text !== original;
  fileName.classList.toggle("modified", modified);
  resetBtn.hidden = !modified;
  setStatus("busy", "Translating…");
  translateSoon();
  saveSoon();
};
const translateSoon = debounce(() => void retranslate(), 140);
const saveSoon = debounce(() => storage.set("ariadne-draft", JSON.stringify({ slug: current?.slug ?? null, text: ts.text })), 400);

function setStatus(kind: "busy" | "ok" | "err" | "idle", text: string) {
  fill(status, 
    kind === "busy" ? h("span", { class: "spinner" }) : kind === "ok" ? h("span", { class: "chip ok" }, icon("check"), "Translated")
      : kind === "err" ? h("span", { class: "chip err" }, icon("x"), "Refused") : null,
    h("span", null, text));
}

async function retranslate() {
  const text = ts.text;
  const namespace = current?.namespace ?? "Playground";
  const path = current?.path ?? "playground.ts";
  let result: Translation;
  try {
    result = await translator.translate(text, namespace, path);
  } catch (err) {
    if (ts.text !== text) return;
    setStatus("err", err instanceof Timeout ? "The translator took too long and was restarted" : String((err as Error).message));
    return;
  }
  if (ts.text !== text) return; // A newer edit is on its way.
  const toUtf16 = byteMapper(text);
  ts.hoverProvider = sourceHovers(text, result.hovers, toUtf16);
  ts.setLenses(lenses(text, result.hovers, toUtf16));
  if (result.ok) {
    lastGood = result;
    setStatus("ok", `${result.ms < 10 ? result.ms.toFixed(1) : Math.round(result.ms)} ms`);
    ts.view.dispatch(setDiagnostics(ts.view.state, []));
    fill(dock, );
    showOutputs(text, false);
  } else {
    const d = result.diagnostic;
    const from = toUtf16(d.startByte);
    const to = Math.max(from + 1, toUtf16(d.endByte));
    setStatus("err", `${d.code} · line ${d.line}`);
    ts.view.dispatch(setDiagnostics(ts.view.state, [{ from, to: Math.min(to, text.length), severity: "error", message: `${d.code}: ${d.message}` }]));
    renderDiagnostic(text, d, from, to);
    showOutputs(text, true);
  }
}

function showOutputs(text: string, stale: boolean) {
  const modified = current !== null && text !== original;
  leanEmpty.hidden = !!lastGood;
  if (lastGood) {
    const ciInfo = current?.lean && lastGood.lean === current.lean.text ? current.lean.info : undefined;
    leanView.show(lastGood.lean, {
      info: ciInfo,
      fileName: (current?.lean?.path.split("/").pop()) ?? `${(current?.namespace ?? "Playground").split(".").pop()}.lean`,
      liveNote: stale ? "The program has an error: this is the last translation that succeeded."
        : ciInfo ? undefined : "Translated live, in your browser. Hover names in the TypeScript for what they denote; hover info from Lean is available for the examples as written.",
    });
    if (guards.text !== (lastGood.validators ?? "")) guards.setText(lastGood.validators ?? "// No exported functions.");
    if (!stale) runView.update({ source: text, signatures: lastGood.signatures, validators: lastGood.validators, hovers: lastGood.hovers }, (current as { try?: Presets } | null)?.try, false);
  }
  proofsView.show(current, modified);
  const count = current?.proofs?.info.theorems.length ?? 0;
  const proofsTab = tabButtons.get("proofs")!;
  proofsTab.querySelector(".count")?.remove();
  if (count) proofsTab.append(h("span", { class: "count" }, String(count)));
}

/* ── Hovers and lenses in the TypeScript ────────────────────────────────── */

/** The range of `name` within a declaration's span (the checker logs whole declarations). */
function nameRange(text: string, from: number, to: number, name: string) {
  const re = new RegExp(String.raw`(?<![\w$])${name.replace(/\$/g, "\\$")}(?![\w$])`, "g");
  re.lastIndex = from;
  const m = re.exec(text);
  return m && m.index < to ? { from: m.index, to: m.index + name.length } : null;
}

function leanSignature(x: Hover) {
  const params = (x.params ?? []).map((p) => `(${p.name === "this" ? "«this»" : `«${p.name}»`} : ${p.lean})`).join(" ");
  return `def «${x.name}»${params ? " " + params : ""} : ${x.lean}`;
}

function sourceHovers(text: string, hovers: Hover[], toUtf16: (b: number) => number): HoverProvider {
  const ranges = hovers.map((x) => {
    let from = toUtf16(x.start), to = toUtf16(x.stop);
    if (x.kind !== "expr" && x.name) {
      const r = nameRange(text, from, to, x.name);
      if (!r) return null;
      ({ from, to } = r);
    }
    return { from, to, x };
  }).filter((r): r is NonNullable<typeof r> => r !== null);
  return (pos) => {
    if (ts.text !== text) return null;
    let best: (typeof ranges)[number] | null = null;
    for (const r of ranges) if (r.from <= pos && pos <= r.to && (!best || r.to - r.from < best.to - best.from)) best = r;
    if (!best) return null;
    const { x } = best;
    const row = (label: string, value: string) => h("div", { class: "hover-row" }, h("span", null, label), h("code", null, value));
    const dom = h("div", { class: "hover" });
    if (x.kind === "function" || x.kind === "method") {
      dom.append(h("div", { class: "hover-sig" }, leanSignature(x)),
        row("Theorem", `«${x.name}».source: every run converges to this definition's value${x.safe ? `, when «${x.name}».safe holds` : ""}`),
        row("Safety", x.safe ? `«${x.name}».safe (see the Lean tab)` : "always safe: nothing can leave the model"));
    } else if (x.kind === "var") {
      dom.append(h("div", { class: "hover-sig" }, `${x.name}: ${x.ts}`), row("Lean", `«${x.name}» : ${x.lean}`));
    } else {
      dom.append(row("TypeScript", x.ts), row("Lean", x.lean));
      if (x.term) dom.append(row("Denotes", x.term));
      if (x.safe) dom.append(row("Safe when", x.safe));
    }
    dom.append(h("div", { class: "hover-note" }, "From Ariadne's checker, live as you type."));
    return { from: best.from, to: best.to, dom };
  };
}

function lenses(text: string, hovers: Hover[], toUtf16: (b: number) => number): Lens[] {
  return hovers.filter((x) => x.kind === "function" || x.kind === "method").map((x) => {
    const r = nameRange(text, toUtf16(x.start), toUtf16(x.stop), x.name!);
    const arrow = [...(x.params ?? []).map((p) => p.lean), x.lean].join(" → ");
    return {
      pos: r?.from ?? toUtf16(x.start),
      dom: () => h("div", { class: "cm-lens", title: "Open in the Lean tab", style: "cursor:pointer",
        onclick: () => { selectTab("lean"); showPane("right"); leanView.revealDefinition(x.name!); } },
        h("span", { class: "lean" }, `«${x.name}» : ${arrow}`),
        h("span", { class: `safe ${x.safe ? "cond" : "always"}` }, x.safe ? `safe when «${x.name}».safe` : "always safe")),
    };
  });
}

/* ── Diagnostics ────────────────────────────────────────────────────────── */

function renderDiagnostic(text: string, d: Extract<Translation, { ok: false }>["diagnostic"], from: number, to: number) {
  const e = explain({ code: d.code, message: d.message, snippet: text.slice(from, to), from, to, source: text });
  const jump = () => { ts.view.dispatch({ selection: { anchor: from, head: to }, scrollIntoView: true }); ts.view.focus(); };
  fill(dock, h("div", { class: "diag" },
    h("div", { class: "diag-head" },
      h("span", { class: "diag-icon" }, icon("x")),
      h("div", null,
        h("div", { class: "diag-title" }, d.message.charAt(0).toUpperCase() + d.message.slice(1)),
        h("div", { class: "diag-loc" }, h("span", { class: "mono" }, d.code), h("span", null, `line ${d.line}, column ${d.column}`),
          h("button", { onclick: jump }, "Show")))),
    d.notes.length || d.help ? h("ul", { class: "diag-notes" }, ...d.notes.map((n) => h("li", null, n)), d.help && !e ? h("li", null, d.help) : null) : null,
    e ? h("div", { class: "diag-explain" },
      h("h4", null, icon("info"), e.title),
      h("p", null, ...inlineCode(e.why)),
      e.before || e.after ? h("div", { class: "diag-fix" },
        e.before ? h("div", { class: "before" }, e.before) : null,
        e.after ? h("div", { class: "after" }, e.after) : null) : null,
      h("div", { class: "diag-actions" },
        e.fix ? h("button", { class: "btn small thread", onclick: () => ts.replace(e.fix!.from, e.fix!.to, e.fix!.insert) }, icon("wand"), "Apply the fix") : null,
        e.guide ? h("button", { class: "btn small", onclick: () => { selectTab("subset"); showPane("right"); void subsetView.focus(e.guide!); } }, icon("book"), "In the subset guide") : null))
      : h("div", { class: "diag-actions" }, h("button", { class: "btn small", onclick: () => { selectTab("subset"); showPane("right"); } }, icon("book"), "What the subset accepts"))));
}

function inlineCode(text: string): (string | Node)[] {
  return text.split(/(`[^`]+`)/).map((part) => part.startsWith("`") ? h("code", null, part.slice(1, -1)) : part);
}

/* ── Examples ───────────────────────────────────────────────────────────── */

async function open(slug: string | null, text?: string) {
  try {
    current = slug ? await loadExample(slug) : null;
  } catch {
    current = null;
  }
  original = current?.source ?? BLANK;
  const doc = text ?? original;
  exampleBtn.querySelector(".title")!.textContent = current?.title ?? "Your code";
  fileName.querySelector(".name")!.textContent = current?.path.split("/").pop() ?? "playground.ts";
  lastGood = null;
  ts.setText(doc);
  if (current) runView.update({ source: "", signatures: [], validators: null }, (current as { try?: Presets }).try, true);
  onEdit();
  await retranslate();
  if (!current?.proofs && tab === "proofs") selectTab("lean");
}

function restore() {
  if (!current) return;
  ts.setText(original);
  onEdit();
}

function openGallery() {
  document.querySelector(".popover")?.remove();
  const rect = exampleBtn.getBoundingClientRect();
  const close = () => { pop.remove(); document.removeEventListener("click", outside); document.removeEventListener("keydown", esc); };
  const outside = (e: MouseEvent) => { if (!pop.contains(e.target as Node)) close(); };
  const esc = (e: KeyboardEvent) => { if (e.key === "Escape") close(); };
  const card = (ex: ExampleMeta) => h("button", { class: `card${current?.slug === ex.slug ? " current" : ""}`,
    onclick: () => { close(); void open(ex.slug); history.replaceState(null, "", `#example=${ex.slug}`); } },
    h("h3", null, ex.title),
    h("p", null, ex.summary),
    h("div", { class: "meta" }, h("span", { class: `chip ${ex.size === "Large" ? "thread" : ex.size === "Medium" ? "info" : ""}` }, ex.size),
      h("span", { class: "chip" }, `${ex.lines} lines`),
      ex.theorems ? h("span", { class: "chip ok" }, icon("shield"), `${ex.theorems} theorems`) : h("span", { class: "chip warn" }, icon("alert"), "refused")));
  const pop = h("div", { class: "popover", role: "dialog", "aria-label": "Examples" },
    h("div", { class: "gallery-head" }, h("h2", null, "Examples"), h("p", null, "Every proof is kernel-checked in CI")),
    h("div", { class: "gallery" }, ...examples.map(card),
      h("button", { class: `card blank${current === null ? " current" : ""}`, onclick: () => { close(); void open(null); history.replaceState(null, "", "#"); } },
        h("h3", null, "Your own"), h("p", null, "Start from a small program and write your own."),
        h("div", { class: "meta" }, h("span", { class: "chip" }, "Your code")))));
  pop.style.top = `${rect.bottom + 8}px`;
  pop.style.left = `${Math.max(12, Math.min(rect.left, innerWidth - Math.min(760, innerWidth - 24) - 12))}px`;
  document.body.append(pop);
  setTimeout(() => { document.addEventListener("click", outside); document.addEventListener("keydown", esc); });
  (pop.querySelector(".card.current") as HTMLElement ?? pop.querySelector(".card") as HTMLElement)?.focus();
}

/* ── Share links ────────────────────────────────────────────────────────── */

async function compress(text: string) {
  const stream = new Blob([text]).stream().pipeThrough(new CompressionStream("deflate-raw"));
  const bytes = new Uint8Array(await new Response(stream).arrayBuffer());
  let bin = "";
  for (const b of bytes) bin += String.fromCharCode(b);
  return btoa(bin).replace(/\+/g, "-").replace(/\//g, "_").replace(/=+$/, "");
}

async function decompress(code: string) {
  const bin = atob(code.replace(/-/g, "+").replace(/_/g, "/"));
  const bytes = Uint8Array.from(bin, (c) => c.charCodeAt(0));
  const stream = new Blob([bytes]).stream().pipeThrough(new DecompressionStream("deflate-raw"));
  return new Response(stream).text();
}

async function share() {
  const text = ts.text;
  let hash = current && text === original ? `example=${current.slug}` : `code=${await compress(text)}`;
  if (current && text !== original) hash = `example=${current.slug}&${hash}`;
  history.replaceState(null, "", `#${hash}`);
  toast(await copyText(location.href) ? "Link copied" : "Link in the address bar");
}

/* ── Intro ──────────────────────────────────────────────────────────────── */

function renderIntro() {
  if (storage.get("ariadne-intro") === "seen") return;
  fill(introSlot, h("div", { class: "intro" },
    h("button", { class: "btn icon ghost close", "aria-label": "Dismiss", onclick: () => { storage.set("ariadne-intro", "seen"); fill(introSlot, ); } }, icon("x")),
    h("h2", null, "TypeScript in, Lean out, with a proof that they agree"),
    h("p", null, "Ariadne translates a subset of TypeScript into readable Lean definitions. One theorem, proved once in Lean, says that running the JavaScript gives what the definitions compute, so what you prove about them holds of the code. Everything here runs in your browser."),
    h("ol", null,
      h("li", null, "Edit the code: the translation updates as you type. Hover a name for what it denotes."),
      h("li", null, h("b", null, "Lean"), " shows the definitions, safety conditions and the theorem for each function."),
      h("li", null, h("b", null, "Proofs"), " steps through kernel-checked proofs about the examples."),
      h("li", null, h("b", null, "Run"), " calls the code in the model and as real JavaScript, and compares."))));
}

/* ── Start ──────────────────────────────────────────────────────────────── */

async function start() {
  selectTab(tab in views ? tab : "lean");
  setStatus("busy", "Loading the translator…");
  const [index, info] = await Promise.all([
    fetch("data/examples.json").then((r) => r.json()) as Promise<ExampleMeta[]>,
    fetch("data/build.json").then((r) => r.json()).catch(() => build) as Promise<BuildInfo>,
    translator.ready(),
  ]);
  examples = index;
  build = info;
  (document.querySelector(".version") as HTMLElement).textContent = `v${build.version}`;
  fill(footer, 
    h("span", null, `Ariadne ${build.version}`), h("span", { class: "sep" }, "·"),
    h("span", null, build.lean.replace("leanprover/lean4:", "Lean ")), h("span", { class: "sep hide-narrow" }, "·"),
    h("span", { class: "hide-narrow" }, "The translator and the model run in your browser, compiled to WebAssembly"),
    h("span", { class: "spacer" }),
    build.commit ? h("a", { href: `${REPO}/commit/${build.commit}`, target: "_blank", rel: "noopener" }, build.commit.slice(0, 7)) : null);
  renderIntro();

  const params = new URLSearchParams(location.hash.slice(1));
  const slug = params.get("example");
  const code = params.get("code");
  if (code) {
    try { await open(slug, await decompress(code)); return; } catch { toast("That link's code could not be read"); }
  }
  if (slug && examples.some((e) => e.slug === slug)) { await open(slug); return; }
  const draft = storage.get("ariadne-draft");
  if (draft) {
    try {
      const d = JSON.parse(draft) as { slug: string | null; text: string };
      await open(d.slug && examples.some((e) => e.slug === d.slug) ? d.slug : null, d.text);
      return;
    } catch {}
  }
  await open(examples[0]?.slug ?? null);
}

start().catch((err) => {
  console.error(err);
  setStatus("err", `Could not start: ${(err as Error).message}`);
});
