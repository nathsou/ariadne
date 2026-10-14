// Clients of the two workers. A call that runs past its time limit (a loop that does not end, in the
// model or in JavaScript) terminates the worker; the next call starts a fresh one.
import type { Obs, Translation } from "./types";

class Rpc {
  private worker: Worker | null = null;
  private next = 0;
  private pending = new Map<number, { resolve: (v: any) => void; reject: (e: Error) => void }>();
  /** Called after the worker was restarted (its state is gone). */
  onRestart: () => void = () => {};

  constructor(private url: string) {}

  private start(): Worker {
    if (this.worker) return this.worker;
    const w = new Worker(this.url, { type: "module" });
    w.onmessage = (e) => {
      const p = this.pending.get(e.data.id);
      if (!p) return;
      this.pending.delete(e.data.id);
      if (e.data.ok) p.resolve(e.data.result);
      else p.reject(new Error(e.data.error));
    };
    w.onerror = (e) => {
      e.preventDefault();
      this.restart(new Error(e.message || "the worker crashed"));
    };
    this.worker = w;
    return w;
  }

  private restart(reason: Error) {
    this.worker?.terminate();
    this.worker = null;
    for (const p of this.pending.values()) p.reject(reason);
    this.pending.clear();
    this.onRestart();
  }

  call<T>(message: Record<string, unknown>, timeoutMs: number): Promise<T> {
    const w = this.start();
    const id = this.next++;
    return new Promise<T>((resolve, reject) => {
      const timer = setTimeout(() => this.restart(new Timeout(timeoutMs)), timeoutMs);
      this.pending.set(id, {
        resolve: (v) => { clearTimeout(timer); resolve(v); },
        reject: (e) => { clearTimeout(timer); reject(e); },
      });
      w.postMessage({ ...message, id });
    });
  }
}

export class Timeout extends Error {
  constructor(public ms: number) {
    super(`stopped after ${ms / 1000}s`);
  }
}

const here = new URL("./", document.baseURI);

export const translator = new (class {
  private rpc = new Rpc(new URL("translator.worker.js", here).href);
  ready() {
    return this.rpc.call<void>({ op: "init" }, 120000);
  }
  translate(source: string, namespace: string, path: string) {
    return this.rpc.call<Translation>({ op: "translate", source, namespace, path }, 8000);
  }
  /** Calls in the model, as lines of `ariadne batch` (each `["f", args...]` or `["@m", state, args...]`). */
  run(source: string, calls: string[], timeoutMs = 10000) {
    return this.rpc.call<Obs[]>({ op: "run", source, calls }, timeoutMs);
  }
})();

export const javascript = new (class {
  private rpc = new Rpc(new URL("js.worker.js", here).href);
  private loaded: string | null = null;
  constructor() {
    this.rpc.onRestart = () => { this.loaded = null; };
  }
  async load(source: string, validators: string | null) {
    const key = source + "\0" + (validators ?? "");
    if (this.loaded === key) return;
    await this.rpc.call<string[]>({ op: "load", source, validators }, 5000);
    this.loaded = key;
  }
  call(name: string, args: string[]) {
    return this.rpc.call<{ args: Obs[]; valid: boolean | null; value?: Obs; throws?: string }>({ op: "call", name, args }, 3000);
  }
  create(cls: string, session: number) {
    return this.rpc.call<{ state: Obs }>({ op: "new", class: cls, session }, 3000);
  }
  method(session: number, name: string, args: string[]) {
    return this.rpc.call<{ before: Obs; args: Obs[]; valid: boolean | null; value?: Obs; throws?: string; state: Obs }>(
      { op: "method", session, name, args }, 3000);
  }
  fuzz(signatures: unknown[], perFunction: number, seed: number) {
    return this.rpc.call<{ fn: string; text: string; line: string; expected: Obs }[]>(
      { op: "fuzz", signatures, perFunction, seed }, 15000);
  }
})();
