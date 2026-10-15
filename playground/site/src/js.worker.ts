// Runs the program as JavaScript: TypeScript types stripped (Sucrase), loaded as a module, called on
// values the page describes. Values cross to the page as observations (`scripts/observe.mjs`), the
// form the model takes and gives, so the two can be compared exactly.
import { transform } from "sucrase";
// @ts-ignore: plain JavaScript shared with the repository's differential test.
import { observe } from "../../../scripts/observe.mjs";
// @ts-ignore
import { values } from "../../../scripts/values.mjs";

type Mod = Record<string, any>;
let program: Mod | null = null;
let guards: Mod | null = null;
const sessions = new Map<number, any>();

async function load(ts: string): Promise<Mod> {
  const js = transform(ts, { transforms: ["typescript"], disableESTransforms: true }).code;
  const url = URL.createObjectURL(new Blob([js], { type: "text/javascript" }));
  try {
    return await import(url);
  } finally {
    URL.revokeObjectURL(url);
  }
}

/** A value written as a JavaScript expression (`[1, 2]`, `{ a: 1 }`, `new Map([["k", 1]])`, `3n`). */
function evaluate(expr: string): unknown {
  return new Function(`"use strict"; return (${expr.trim() === "" ? "undefined" : expr});`)();
}

function attempt(f: () => unknown) {
  try {
    return { value: observe(f()) };
  } catch (err) {
    return { throws: `${(err as Error)?.name ?? "Error"}: ${(err as Error)?.message ?? err}` };
  }
}

const valid = (name: string, args: unknown[]) => {
  const g = guards?.args?.[name];
  if (typeof g !== "function") return null;
  try { return Boolean(g(...args)); } catch { return false; }
};

self.onmessage = async (e: MessageEvent) => {
  const { id, op } = e.data;
  try {
    let result: unknown;
    if (op === "load") {
      program = await load(e.data.source);
      guards = e.data.validators ? await load(e.data.validators) : null;
      sessions.clear();
      result = Object.keys(program);
    } else if (op === "call") {
      if (!program) throw new Error("no program");
      const args = (e.data.args as string[]).map(evaluate);
      const f = program[e.data.name];
      if (typeof f !== "function") throw new Error(`'${e.data.name}' is not exported`);
      result = { args: args.map(observe), valid: valid(e.data.name, args), ...attempt(() => f(...args)) };
    } else if (op === "new") {
      if (!program) throw new Error("no program");
      const cls = program[e.data.class];
      const self_ = new cls();
      sessions.set(e.data.session, self_);
      result = { state: observe(self_) };
    } else if (op === "method") {
      const self_ = sessions.get(e.data.session);
      if (!self_) throw new Error("no object");
      const before = observe(self_);
      const args = (e.data.args as string[]).map(evaluate);
      const out = attempt(() => self_[e.data.name](...args));
      result = { before, args: args.map(observe), valid: valid(e.data.name, args), ...out, state: observe(self_) };
    } else if (op === "fuzz") {
      // The differential test (`scripts/differential.mjs`), in the browser: random inputs of the declared
      // types, run here; the page runs the same calls in the model and compares.
      if (!program) throw new Error("no program");
      const { value } = values(e.data.seed);
      const calls: { fn: string; text: string; line: string; expected: unknown }[] = [];
      for (const sig of e.data.signatures) {
        if (!sig.exported) continue;
        for (let i = 0; i < e.data.perFunction; i++) {
          if (sig.method) {
            const cls = program[sig.class];
            const self_ = Object.create(cls.prototype);
            for (const [name, ty] of sig.params[0].fields) self_[name] = value(ty);
            const before = observe(self_);
            const args = sig.params.slice(1).map(value);
            let expected: unknown;
            try { expected = ["method", observe(self_[sig.name](...args)), observe(self_)]; }
            catch (err) { expected = ["throws", String(err)]; }
            calls.push({ fn: `${sig.class}.${sig.name}`, text: `${sig.name}(${args.map(show).join(", ")})`,
              line: JSON.stringify(["@" + sig.name, before, ...args.map(observe)]), expected });
          } else if (sig.class !== null) {
            if (i > 0) continue;
            let expected: unknown;
            try { expected = observe(new program[sig.class]()); } catch (err) { expected = ["throws", String(err)]; }
            calls.push({ fn: sig.name, text: sig.name + "()", line: JSON.stringify([sig.name]), expected });
          } else {
            let args = sig.params.map(value);
            while (args.length > 0 && args[args.length - 1] === undefined && Math.random() < 0.5) args = args.slice(0, -1);
            let expected: unknown;
            try { expected = observe(program[sig.name](...args)); } catch (err) { expected = ["throws", String(err)]; }
            calls.push({ fn: sig.name, text: `${sig.name}(${args.map(show).join(", ")})`,
              line: JSON.stringify([sig.name, ...args.map(observe)]), expected });
          }
        }
      }
      result = calls;
    }
    self.postMessage({ id, ok: true, result });
  } catch (err) {
    self.postMessage({ id, ok: false, error: `${(err as Error)?.name ?? "Error"}: ${(err as Error)?.message ?? err}` });
  }
};

function show(v: unknown): string {
  return JSON.stringify(v, (_, x) => typeof x === "bigint" ? `${x}n` : x === undefined ? "undefined" :
    x instanceof Map ? Object.fromEntries(x) : x) ?? "undefined";
}
