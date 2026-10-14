// The translator, compiled to WebAssembly (`wasm/build.sh`), in a worker so a long call never blocks
// the page (the page restarts the worker when one runs too long).
type Module = {
  _ariadne_init(): number;
  _ariadne_translate(text: number, ns: number, path: number): number;
  _ariadne_run(text: number, call: number): number;
  _free(p: number): void;
  stringToNewUTF8(s: string): number;
  UTF8ToString(p: number): string;
};

const base = new URL("./", self.location.href);
const ready: Promise<Module> = (async () => {
  const { default: create } = await import(new URL("ariadne.js", base).href);
  const mod: Module = await create({
    locateFile: (p: string) => new URL(p, base).href,
    print: () => {},
    printErr: (s: string) => console.warn("[ariadne]", s),
  });
  if (!mod._ariadne_init()) throw new Error("the translator failed to initialize");
  return mod;
})();

function call(mod: Module, f: (...ptrs: number[]) => number, ...args: string[]): string {
  const ptrs = args.map((a) => mod.stringToNewUTF8(a));
  try {
    const out = f.apply(mod, ptrs);
    const text = mod.UTF8ToString(out);
    mod._free(out);
    return text;
  } finally {
    for (const p of ptrs) mod._free(p);
  }
}

self.onmessage = async (e: MessageEvent) => {
  const { id, op } = e.data;
  try {
    const mod = await ready;
    if (op === "init") {
      self.postMessage({ id, ok: true });
    } else if (op === "translate") {
      const started = performance.now();
      const json = call(mod, mod._ariadne_translate, e.data.source, e.data.namespace, e.data.path);
      self.postMessage({ id, ok: true, result: { ...JSON.parse(json), ms: performance.now() - started } });
    } else if (op === "run") {
      const results = (e.data.calls as string[]).map((c) => JSON.parse(call(mod, mod._ariadne_run, e.data.source, c)));
      self.postMessage({ id, ok: true, result: results });
    }
  } catch (err) {
    self.postMessage({ id, ok: false, error: String((err as Error)?.message ?? err) });
  }
};
