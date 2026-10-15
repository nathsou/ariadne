// The Run tab: each call runs twice, in Ariadne's model of JavaScript (the trusted base, compiled to
// WebAssembly with the translator) and as the real JavaScript in this browser, and the results are
// compared. The source theorem says they agree on every input where the safety condition holds.
import { javascript, translator } from "./workers";
import type { Hover, Obs, Signature } from "./types";
import { faultText, sameObs, sample, showObs, showTy } from "./values";
import { fill, h, icon, leanIdent } from "./util";

export type Presets = Record<string, string[] | string[][]>;

interface Program { source: string; signatures: Signature[]; validators: string | null; hovers?: Hover[] }

export class RunView {
  el: HTMLElement;
  private list = h("div", { class: "run" });
  private program: Program | null = null;
  private inputs = new Map<string, string[]>();
  private fuzzOut = h("div", { class: "fuzz-report" });
  private sessions = 0;

  constructor() {
    this.el = h("div", { class: "view" }, h("div", { class: "scroll" }, this.list));
  }

  update(program: Program, presets: Presets | undefined, fresh: boolean) {
    const same = this.program && this.program.source === program.source;
    this.program = program;
    if (fresh) {
      this.inputs.clear();
      for (const [k, v] of Object.entries(presets ?? {})) if (!k.startsWith("@")) this.inputs.set(k, v as string[]);
    }
    if (same) return;
    this.render(presets);
  }

  private render(presets: Presets | undefined) {
    const p = this.program!;
    const fns = p.signatures.filter((s) => s.exported && s.class === null);
    const classes = [...new Set(p.signatures.filter((s) => s.class !== null).map((s) => s.class!))];
    fill(this.fuzzOut, );
    const intro = h("div", { class: "run-intro" },
      h("p", null, h("b", null, "Two runs, one answer. "),
        "Each call runs in Ariadne's model of JavaScript, the one the theorem is about, and as the real JavaScript in this browser. The source theorem says they agree wherever the safety condition holds; the random test checks it on hundreds of inputs."),
      h("button", { class: "btn thread", onclick: () => this.fuzz() }, icon("dice"), "Random test"));
    fill(this.list, intro, this.fuzzOut,
      ...fns.map((s) => this.fnCard(s)),
      ...classes.map((c) => this.classCard(c, presets?.["@" + c] as string[][] | undefined)));
    if (fns.length === 0 && classes.length === 0) {
      this.list.append(h("div", { class: "empty-state" }, icon("play"), h("h3", null, "Nothing to run"),
        h("p", null, "Export a function (or a class) to call it here.")));
    }
  }

  private fnCard(sig: Signature) {
    const d = describe(this.program!, sig);
    const names = d.names;
    const values = this.inputs.get(sig.name) ?? sig.params.map((t) => sample(t));
    this.inputs.set(sig.name, values);
    const out = h("div");
    const fields = sig.params.map((ty, i) => {
      const input = h("input", { value: values[i] ?? "", spellcheck: "false", "aria-label": names[i] ?? `argument ${i + 1}`,
        placeholder: d.types[i], title: d.types[i],
        oninput: (e: Event) => { values[i] = (e.target as HTMLInputElement).value; },
        onkeydown: (e: KeyboardEvent) => { if (e.key === "Enter") run(); } }) as HTMLInputElement;
      void ty;
      return h("div", { class: "arg" }, h("label", { title: d.types[i] }, names[i] ?? `arg${i}`), input);
    });
    const run = async () => {
      fill(out, h("div", { class: "status" }, h("span", { class: "spinner" }), "Running…"));
      fill(out, await this.call(sig, values));
    };
    return h("section", { class: "fn" },
      h("div", { class: "fn-head" }, signatureText(sig.name, names, d.types, d.result), h("span", { class: "spacer" }),
        h("button", { class: "btn small primary", onclick: run }, icon("play"), "Run")),
      h("div", { class: "fn-body" }, ...fields, out));
  }

  private async call(sig: Signature, args: string[]): Promise<HTMLElement> {
    const p = this.program!;
    try {
      await javascript.load(p.source, p.validators);
      const js = await javascript.call(sig.name, args);
      const [model] = await translator.run(p.source, [JSON.stringify([sig.name, ...js.args])]);
      return comparison(sig.name, model, js.value ?? ["throws", js.throws!], js.valid);
    } catch (err) {
      return verdict("err", `${(err as Error).message}`, "Check the arguments: each is a JavaScript expression.");
    }
  }

  private classCard(cls: string, preset: string[][] | undefined) {
    const p = this.program!;
    const methods = p.signatures.filter((s) => s.class === cls && s.method);
    const ctor = p.signatures.find((s) => s.class === cls && !s.method);
    let session = -1;
    let modelState: Obs | null = null;
    const stateBox = h("div");
    const steps = h("div", { class: "session" });
    const argBox = h("div", { class: "fn-body" });
    const select = h("select", { "aria-label": "Method", onchange: () => renderArgs() },
      ...methods.map((m) => h("option", { value: m.name }, m.name))) as HTMLSelectElement;
    let argValues: string[] = [];
    const renderArgs = (preset?: string[]) => {
      const sig = methods.find((m) => m.name === select.value)!;
      const d = describe(p, sig);
      const names = d.names.slice(1);
      argValues = preset ?? sig.params.slice(1).map((t) => sample(t));
      fill(argBox, ...sig.params.slice(1).map((_, i) => h("div", { class: "arg" },
        h("label", { title: d.types[i + 1] }, names[i] ?? `arg${i}`),
        h("input", { value: argValues[i], spellcheck: "false", oninput: (e: Event) => { argValues[i] = (e.target as HTMLInputElement).value; },
          onkeydown: (e: KeyboardEvent) => { if (e.key === "Enter") call(); } }))));
    };
    const reset = async () => {
      fill(steps, );
      try {
        await javascript.load(p.source, p.validators);
        session = this.sessions++;
        const js = await javascript.create(cls, session);
        const [model] = await translator.run(p.source, [JSON.stringify([ctor?.name ?? `new ${cls}`])]);
        modelState = model;
        fill(stateBox, stateView(model), sameObs(model, js.state) ? null
          : verdict("err", "The model's new object differs from JavaScript's.", showObs(js.state)));
        steps.append(h("div", { class: "step" }, h("span", { class: "idx" }, "0"), h("span", null, `new ${cls}()`), h("span", { class: "chip ok" }, icon("check"), "agree")));
      } catch (err) {
        fill(stateBox, verdict("err", (err as Error).message, ""));
      }
    };
    const call = async (name = select.value, args = argValues) => {
      if (session < 0 || !modelState) await reset();
      const sig = methods.find((m) => m.name === name)!;
      try {
        const js = await javascript.method(session, name, args);
        const [model] = await translator.run(p.source, [JSON.stringify(["@" + name, modelState, ...js.args])]);
        const n = steps.children.length;
        const text = `${name}(${js.args.map((a) => showObs(a)).join(", ")})`;
        if (model[0] === "method") {
          const [, result, state] = model as [string, Obs, Obs];
          const agree = js.value !== undefined && sameObs(result, js.value) && sameObs(state, js.state);
          modelState = state;
          steps.append(h("div", { class: "step" }, h("span", { class: "idx" }, String(n)),
            h("span", null, text, sig.void ? null : h("span", { class: "ret" }, `  → ${showObs(result)}`)),
            agree ? h("span", { class: "chip ok" }, icon("check"), "agree")
              : h("span", { class: "chip err", title: `JavaScript: ${js.value ? showObs(js.value) : js.throws}` }, icon("x"), "differ")));
          fill(stateBox, stateView(state), js.valid === false
            ? verdict("info", "These arguments don't represent the declared types.", "The validators reject them; the source theorem assumes they do, so it says nothing about this call.")
            : null);
        } else {
          const f = faultText(String(model[1]));
          steps.append(h("div", { class: "step" }, h("span", { class: "idx" }, String(n)), h("span", null, text),
            h("span", { class: "chip warn" }, icon("alert"), "outside the model")));
          fill(stateBox, stateView(modelState!), verdict(f.outside ? "warn" : "err", f.text, `JavaScript gave ${js.value ? showObs(js.value) : js.throws}.`));
        }
      } catch (err) {
        stateBox.append(verdict("err", (err as Error).message, "Check the arguments: each is a JavaScript expression."));
      }
    };
    renderArgs();
    const run = h("button", { class: "btn small primary", onclick: () => call() }, icon("play"), "Call");
    const card = h("section", { class: "fn" },
      h("div", { class: "fn-head" }, h("span", { class: "fn-sig" }, h("span", { class: "name" }, `new ${cls}()`)),
        h("span", { class: "chip" }, "class"), h("span", { class: "spacer" }),
        preset ? h("button", { class: "btn small", onclick: async () => {
          await reset();
          for (const [name, ...args] of preset) { select.value = name; renderArgs(args); await call(name, args); }
          renderArgs();
        } }, icon("sparkle"), "Play the scenario") : null,
        h("button", { class: "btn small", onclick: reset }, icon("reset"), "New object")),
      h("div", { class: "fn-body" },
        h("p", { class: "empty", style: "margin:0" }, "Call methods on one object: each call runs in JavaScript and in the model, from the same state."),
        h("div", { class: "call-row" }, select, run), argBox, h("div", { class: "goal-title", style: "border-radius:6px" }, "State"), stateBox, steps));
    queueMicrotask(reset);
    return card;
  }

  private async fuzz() {
    const p = this.program;
    if (!p) return;
    fill(this.fuzzOut, h("div", { class: "status" }, h("span", { class: "spinner" }), "Generating inputs and running them in JavaScript…"));
    const started = performance.now();
    try {
      await javascript.load(p.source, p.validators);
      const calls = await javascript.fuzz(p.signatures, 100, (Math.random() * 2 ** 31) | 0);
      fill(this.fuzzOut, h("div", { class: "status" }, h("span", { class: "spinner" }), `Running ${calls.length} calls in the model…`));
      const results: Obs[] = [];
      for (let i = 0; i < calls.length; i += 250) {
        results.push(...await translator.run(p.source, calls.slice(i, i + 250).map((c) => c.line), 20000));
      }
      let agree = 0, outside = 0;
      const differ: { text: string; js: Obs; model: Obs }[] = [];
      results.forEach((r, i) => {
        if (r[0] === "error" && (String(r[1]).startsWith("unsupported:") || r[1] === "timeout")) outside++;
        else if (sameObs(r, calls[i].expected)) agree++;
        else differ.push({ text: calls[i].text, js: calls[i].expected, model: r });
      });
      const total = calls.length;
      const pct = (n: number) => `${(100 * n / total).toFixed(1)}%`;
      fill(this.fuzzOut, 
        h("div", { class: "bar", title: `${agree} agree · ${outside} outside the model · ${differ.length} differ` },
          h("span", { style: `width:${pct(agree)};background:var(--ok)` }),
          h("span", { style: `width:${pct(outside)};background:var(--warn)` }),
          h("span", { style: `width:${pct(differ.length)};background:var(--err)` })),
        differ.length === 0
          ? verdict("ok", `${agree} of ${total} random calls agree`, `${outside ? `${outside} left what the model covers (a number past 2^53, a loop that may not end): its safety condition excludes them. ` : ""}${((performance.now() - started) / 1000).toFixed(1)}s, ${new Set(calls.map((c) => c.fn)).size} functions.`)
          : verdict("err", `${differ.length} of ${total} calls disagree`, "The model and JavaScript differ: that would be a bug in the model. Please report it."),
        ...differ.slice(0, 5).map((d) => h("div", { class: "result" },
          h("div", { class: "result-col" }, h("h5", null, "JavaScript"), h("pre", null, `${d.text}\n→ ${showObs(d.js)}`)),
          h("div", { class: "result-col" }, h("h5", null, "Model"), h("pre", null, showObs(d.model))))));
    } catch (err) {
      fill(this.fuzzOut, verdict("err", (err as Error).message, ""));
    }
  }
}

function comparison(name: string, model: Obs, js: Obs, valid: boolean | null) {
  const cols = h("div", { class: "result" },
    h("div", { class: "result-col" }, h("h5", null, "Model", h("span", null, "Lean's semantics")), h("pre", null, showObs(model))),
    h("div", { class: "result-col" }, h("h5", null, "JavaScript", h("span", null, "this browser")), h("pre", null, showObs(js))));
  let v: HTMLElement;
  if (model[0] === "error") {
    const f = faultText(String(model[1]));
    v = verdict(f.outside ? "warn" : "err", f.outside ? "Outside the model" : "The model failed", f.text);
  } else if (valid === false) {
    v = verdict("info", "These arguments don't represent the declared types.",
      `The generated guard args.${name}(…) rejects them: the source theorem assumes it would accept them, so it claims nothing here.`);
  } else if (sameObs(model, js)) {
    v = verdict("ok", "Same result.", `${leanIdent(name)}.source says so for every input where ${leanIdent(name)}.safe holds, without running anything.`);
  } else {
    v = verdict("err", "The model and JavaScript disagree.", "That would be a bug in the model: please report it.");
  }
  return h("div", { style: "display:grid;gap:8px" }, cols, v);
}

function verdict(kind: "ok" | "err" | "warn" | "info", title: string, detail: string) {
  const ic = { ok: "check", err: "x", warn: "alert", info: "info" }[kind];
  return h("div", { class: `verdict ${kind}` }, icon(ic), h("div", null, h("b", null, title), detail ? " " : null, detail ? h("span", null, detail) : null));
}

function stateView(state: Obs) {
  if (state[0] !== "record") return h("pre", { class: "mono" }, showObs(state));
  const fields = state[1] as [string, Obs][];
  return h("table", { class: "state-table" },
    h("thead", null, h("tr", null, h("th", null, "Field"), h("th", null, "Entries"))),
    h("tbody", null, ...fields.map(([f, v]) => h("tr", null, h("td", null, f), h("td", null, showObs(v))))));
}

function signatureText(name: string, names: string[], types: string[], result: string) {
  return h("span", { class: "fn-sig" }, h("span", { class: "name" }, name), "(",
    ...types.flatMap((t, i) => [i ? ", " : "", `${names[i] ?? `arg${i}`}: `, h("span", { class: "ty" }, t)]),
    "): ", h("span", { class: "ty" }, result));
}

/** Parameter names and types as the source writes them (from the checker's log), else from the signature. */
function describe(p: Program, sig: Signature): { names: string[]; types: string[]; result: string } {
  const x = p.hovers?.find((x) => (x.kind === "function" || x.kind === "method") && x.name === sig.name);
  if (x?.params && x.params.length === sig.params.length) {
    return { names: x.params.map((q) => q.name), types: x.params.map((q) => q.ts), result: sig.void ? "void" : x.ts };
  }
  return { names: paramNames(p.source, sig.name, sig.params.length), types: sig.params.map(showTy), result: showTy(sig.result) };
}

/** Parameter names from the source (signatures give only types). */
function paramNames(source: string, name: string, count: number): string[] {
  const m = new RegExp(String.raw`(?:function\s+${name}|^\s*${name})\s*\(([^)]*)\)`, "m").exec(source);
  const names = m ? m[1].split(",").map((p) => p.trim().split(/[?:\s]/)[0]).filter(Boolean) : [];
  return names.length >= count - 1 ? (names.length === count - 1 ? ["this", ...names] : names) : [];
}
