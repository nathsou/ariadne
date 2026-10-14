// The Lean tab (the generated file) and the Proofs tab, with what Lean said about them in CI.
import { marked } from "marked";
import { CodeView, type HoverProvider } from "./editors";
import type { ExampleData, LeanGoal, LeanInfo, LeanTheorem } from "./types";
import { copyText, download, escapeHtml, fill, h, icon, leanPosMapper, toast } from "./util";

/** Hovers from `lake exe extract`, for a file whose text is the one CI elaborated. */
export function leanHovers(text: string, info: LeanInfo): HoverProvider {
  const at = leanPosMapper(text);
  const ranges = info.hovers
    .map((x) => ({ from: at(x.start), to: at(x.stop), x }))
    .sort((a, b) => a.from - b.from);
  return (pos) => {
    let best: (typeof ranges)[number] | null = null;
    for (const r of ranges) {
      if (r.from > pos) break;
      if (r.to >= pos && (!best || r.to - r.from < best.to - best.from)) best = r;
    }
    if (!best) return null;
    const { x } = best;
    const dom = h("div", { class: "hover" });
    if (x.kind === "local") {
      dom.append(h("div", { class: "hover-sig" }, `${x.name} : ${x.type ?? ""}`));
    } else {
      const c = info.consts[x.name];
      dom.append(h("div", { class: "hover-sig" }, c?.signature ?? x.name));
      if (c?.doc) dom.append(h("div", { class: "hover-doc", html: marked.parse(c.doc, { async: false }) as string }));
    }
    return { from: best.from, to: best.to, dom };
  };
}

/** Lean names, without the example's namespaces. */
export function shortName(name: string, namespaces: string[]) {
  for (const ns of namespaces) if (name.startsWith(ns + ".")) return name.slice(ns.length + 1);
  return name;
}

const standardAxioms = new Set(["propext", "Classical.choice", "Quot.sound"]);

export function axiomChips(t: LeanTheorem): HTMLElement {
  const extra = t.axioms.filter((a) => !standardAxioms.has(a));
  return h("div", { class: "axioms" },
    extra.length === 0
      ? h("span", { class: "chip ok", title: `Axioms: ${t.axioms.join(", ") || "none"}` }, icon("shield"),
          t.axioms.length === 0 ? "no axioms" : "standard axioms only")
      : h("span", { class: "chip err" }, icon("alert"), `uses ${extra.join(", ")}`),
    t.axioms.length ? h("span", null, t.axioms.join(" · ")) : null);
}

/* ── Lean tab ───────────────────────────────────────────────────────────── */

export class LeanView {
  el: HTMLElement;
  private code: CodeView;
  private banner = h("div");
  private stats = h("span");
  private folded = true;
  private foldButton: HTMLButtonElement;
  private name = "Output.lean";

  constructor() {
    this.foldButton = h("button", { class: "btn small ghost", onclick: () => this.toggleFold() }) as HTMLButtonElement;
    const host = h("div", { class: "editor-host" });
    this.el = h("div", { class: "view" },
      this.banner,
      h("div", { class: "toolbar" },
        this.stats, h("span", { class: "grow" }), this.foldButton,
        h("button", { class: "btn small ghost", title: "Copy", onclick: async () => toast(await copyText(this.code.text) ? "Copied the Lean file" : "Copy failed") }, icon("copy"), h("span", { class: "hide-narrow" }, "Copy")),
        h("button", { class: "btn small ghost", title: "Download", onclick: () => download(this.name, this.code.text) }, icon("download"), h("span", { class: "hide-narrow" }, "Download"))),
      host);
    this.code = new CodeView(host, { doc: "", language: "lean", fold: true });
  }

  private toggleFold() {
    this.folded = !this.folded;
    this.code.setMachineryFolded(this.folded);
    this.renderFoldButton();
  }

  private renderFoldButton() {
    fill(this.foldButton, icon(this.folded ? "expand" : "collapse"),
      this.folded ? `Show the checked machinery (${this.code.machineryLines} lines)` : "Fold the machinery");
  }

  show(text: string, opts: { info?: LeanInfo; fileName: string; liveNote?: string }) {
    if (text !== this.code.text) {
      this.code.setText(text, true);
      this.folded = true;
    }
    this.name = opts.fileName;
    this.code.hoverProvider = opts.info ? leanHovers(text, opts.info) : null;
    const lines = text.split("\n").length;
    fill(this.stats, h("span", { class: "lang-badge lean" }, "LEAN"), " ",
      h("span", { class: "mono" }, opts.fileName), ` · ${lines} lines`);
    this.renderFoldButton();
    fill(this.banner, opts.liveNote
      ? h("div", { class: "banner info" }, icon("info"), h("span", { class: "grow" }, opts.liveNote))
      : h("div", { class: "banner ok" }, icon("shield"), h("span", { class: "grow" },
          h("b", null, "Kernel-checked in CI. "), "Hover any name for its type. The folded parts are the syntax tree, typed syntax and equations the kernel checks for this file; the readable definitions, safety conditions and source theorems are what proofs use.")));
  }

  /** Scroll to the readable definition of `name`. */
  revealDefinition(name: string) {
    const text = this.code.text;
    const m = new RegExp(String.raw`^def «${name.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")}»`, "m").exec(text);
    if (m) {
      this.code.reveal(m.index, true);
      this.code.mark({ from: m.index, to: m.index + m[0].length }, "cm-hover-target");
    }
  }
}

/* ── Proofs tab ─────────────────────────────────────────────────────────── */

export class ProofsView {
  el: HTMLElement;
  private code: CodeView;
  private strip = h("div", { class: "theorem-strip", role: "list" });
  private detail = h("div", { class: "theorem-detail" });
  private banner = h("div");
  private infoBody = h("div", { class: "infoview-body" });
  private infoTitle = h("span");
  private body: HTMLElement;
  private empty: HTMLElement;
  private goals: { from: number; to: number; g: LeanGoal }[] = [];
  private theorems: { t: LeanTheorem; from: number; to: number; chip: HTMLElement }[] = [];
  private namespaces: string[] = [];
  private current: LeanTheorem | null = null;

  constructor() {
    const host = h("div", { class: "editor-host" });
    const infoview = h("div", { class: "infoview" },
      h("div", { class: "infoview-head", title: "Drag to resize" }, icon("terminal"), h("b", null, "Goals"), this.infoTitle),
      this.infoBody);
    this.body = h("div", { class: "proofs" }, this.strip, this.detail, host, infoview);
    this.empty = h("div", { class: "empty-state" }, icon("sparkle"), h("h3", null, "No proofs here yet"),
      h("p", null, "Pick an example with proofs from the examples menu. Proofs about your own code are written in Lean, about the readable definitions in the Lean tab: see the guide."),
      h("a", { href: "https://github.com/nathsou/ariadne/blob/main/docs/GUIDE.md", target: "_blank", rel: "noopener" }, "Read the guide"));
    this.el = h("div", { class: "view" }, this.banner, this.body, this.empty);
    this.code = new CodeView(host, { doc: "", language: "lean", onCursor: (pos) => this.cursor(pos) });
    resizable(infoview.firstElementChild as HTMLElement, infoview);
  }

  show(ex: ExampleData | null, modified: boolean) {
    const proofs = ex?.proofs;
    this.body.hidden = !proofs;
    this.empty.hidden = !!proofs;
    if (!proofs || !ex) { fill(this.banner, ); return; }
    this.namespaces = [`${ex.namespace}.Proofs`, ex.namespace, ex.namespace.replace("Generated.", "") + "Spec", "Ariadne"];
    fill(this.banner, modified
      ? h("div", { class: "banner warn" }, icon("alert"), h("span", { class: "grow" },
          h("b", null, "You edited the source. "), "These proofs are about the original program, as CI checked them; the page can translate but cannot run Lean to re-check them. To prove things about your version, translate it and build the proofs with Lean (see the guide)."))
      : h("div", { class: "banner ok" }, icon("shield"), h("span", { class: "grow" },
          h("b", null, `${proofs.info.theorems.length} theorems, checked by Lean's kernel in CI. `),
          "Move the cursor through a proof to see its goals; hover a name for its type.")));
    if (this.code.text !== proofs.text) this.code.setText(proofs.text);
    this.code.hoverProvider = leanHovers(proofs.text, proofs.info);
    const at = leanPosMapper(proofs.text);
    this.goals = proofs.info.goals
      .map((g) => ({ from: at(g.start), to: at(g.stop), g }))
      .sort((a, b) => (a.to - a.from) - (b.to - b.from));
    const sorted = [...proofs.info.theorems].sort((a, b) => a.line - b.line);
    this.theorems = sorted.map((t, i) => {
      const from = at([t.line, 0]);
      const to = i + 1 < sorted.length ? at([sorted[i + 1].line, 0]) : proofs.text.length;
      const chip = h("button", { class: "theorem-chip", role: "listitem", title: t.doc?.trim() ?? "", onclick: () => {
        this.code.reveal(from, true);
        this.code.view.focus();
      } }, icon("check"), shortName(t.name, this.namespaces));
      return { t, from, to, chip };
    });
    fill(this.strip, ...this.theorems.map((x) => x.chip));
    this.current = null;
    this.selectTheorem(this.theorems[0]?.t ?? null);
    this.renderGoals(null);
  }

  private selectTheorem(t: LeanTheorem | null) {
    if (t === this.current) return;
    this.current = t;
    for (const x of this.theorems) x.chip.classList.toggle("active", x.t === t);
    if (!t) { fill(this.detail, ); return; }
    this.theorems.find((x) => x.t === t)?.chip.scrollIntoView({ block: "nearest", inline: "nearest" });
    fill(this.detail, 
      t.doc ? h("div", { class: "thm-doc", html: marked.parse(t.doc, { async: false }) as string }) : null,
      h("pre", null, this.simplify(t.statement)),
      axiomChips(t));
  }

  private simplify(statement: string) {
    let s = statement;
    for (const ns of this.namespaces) s = s.split(ns + ".").join("");
    return s;
  }

  private cursor(pos: number) {
    const th = this.theorems.find((x) => x.from <= pos && pos < x.to);
    if (th) this.selectTheorem(th.t);
    const g = this.goals.find((x) => x.from <= pos && pos <= x.to);
    this.code.mark(g ? { from: g.from, to: g.to } : null);
    this.renderGoals(g?.g ?? null, g ? this.code.view.state.sliceDoc(g.from, g.to) : "");
  }

  private renderGoals(g: LeanGoal | null, tactic = "") {
    if (!g) {
      this.infoTitle.textContent = "";
      fill(this.infoBody, h("p", { class: "empty" }, "Put the cursor on a tactic to see the goals before and after it."));
      return;
    }
    const first = tactic.split("\n")[0];
    this.infoTitle.textContent = ` · at ${first.length > 48 ? first.slice(0, 48) + "…" : first}`;
    const goalBox = (title: string, goals: string[]) => goals.length === 0
      ? h("div", { class: "goals-done" }, icon("check"), title === "After" ? "No goals: this closes the proof (or this branch)." : "No goals")
      : h("div", { class: "goal" }, h("div", { class: "goal-title" }, `${title} · ${goals.length} goal${goals.length > 1 ? "s" : ""}`),
          ...goals.map((x) => h("pre", { html: colorGoal(x) })));
    fill(this.infoBody, goalBox("Before", g.before), goalBox("After", g.after));
  }
}

function colorGoal(goal: string) {
  return goal.split("\n").map((line) => {
    const e = escapeHtml(line);
    if (line.startsWith("⊢")) return `<span class="turnstile">⊢</span>${e.slice(1)}`;
    const m = e.match(/^(\S[^:]*?)( : .*)$/);
    return m && !line.startsWith(" ") ? `<span class="hyp">${m[1]}</span>${m[2]}` : e;
  }).join("\n");
}

/** Lets `handle` resize `target`'s height by dragging. */
function resizable(handle: HTMLElement, target: HTMLElement) {
  handle.addEventListener("pointerdown", (e) => {
    const start = e.clientY;
    const height = target.getBoundingClientRect().height;
    const parent = target.parentElement!.getBoundingClientRect().height;
    handle.setPointerCapture(e.pointerId);
    const move = (m: PointerEvent) => {
      const next = Math.min(parent * 0.8, Math.max(90, height + start - m.clientY));
      target.style.setProperty("--info-h", `${next}px`);
    };
    const up = () => { handle.removeEventListener("pointermove", move); handle.removeEventListener("pointerup", up); };
    handle.addEventListener("pointermove", move);
    handle.addEventListener("pointerup", up);
  });
}
