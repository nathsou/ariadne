// Observations and types as people read them.
import type { Obs, Ty } from "./types";
import { fromUnits } from "./util";

const quote = (units: number[]) => JSON.stringify(fromUnits(units));

/** An observation as JavaScript would print the value (`{ name: "a", score: 3 }`, `Map { "k" => 1 }`). */
export function showObs(o: Obs, indent = 0): string {
  const pad = "  ".repeat(indent + 1);
  const close = "  ".repeat(indent);
  switch (o[0]) {
    case "undefined": return "undefined";
    case "null": return "null";
    case "bool": return String(o[1]);
    case "number": return String(o[1]);
    case "bigint": return `${o[1]}n`;
    case "string": return quote(o[1] as number[]);
    case "function": return "[function]";
    case "array": {
      const xs = (o[1] as Obs[]).map((x) => showObs(x, indent + 1));
      if (xs.length === 0) return "[]";
      const flat = `[${xs.join(", ")}]`;
      return flat.length <= 72 && !flat.includes("\n") ? flat : `[\n${pad}${xs.join(`,\n${pad}`)}\n${close}]`;
    }
    case "record": {
      const fs = (o[1] as [string, Obs][]).map(([k, v]) => `${/^[A-Za-z_$][\w$]*$/.test(k) ? k : JSON.stringify(k)}: ${showObs(v, indent + 1)}`);
      if (fs.length === 0) return "{}";
      const flat = `{ ${fs.join(", ")} }`;
      return flat.length <= 72 && !flat.includes("\n") ? flat : `{\n${pad}${fs.join(`,\n${pad}`)}\n${close}}`;
    }
    case "map": {
      const es = (o[1] as [number[], Obs][]).map(([k, v]) => `${quote(k)} => ${showObs(v, indent + 1)}`);
      return es.length === 0 ? "Map {}" : `Map { ${es.join(", ")} }`;
    }
    case "method": return showObs(o[1] as Obs, indent);
    case "error": return String(o[1]);
    case "throws": return String(o[1]);
    default: return JSON.stringify(o);
  }
}

export const sameObs = (a: unknown, b: unknown) => JSON.stringify(a) === JSON.stringify(b);

/** A type as TypeScript writes it. */
export function showTy(ty: Ty): string {
  switch (ty.t) {
    case "bool": return "boolean";
    case "bigint": case "number": case "string": return ty.t;
    case "tag": return "bool" in ty && ty.bool !== undefined ? String(ty.bool) : quote(ty.value ?? []);
    case "lits": return ty.values.map(quote).join(" | ");
    case "option": return `${showTy(ty.of)} | ${ty.nullish === "undef" ? "undefined" : ty.nullish === "null" ? "null" : "null | undefined"}`;
    case "record": return `{ ${ty.fields.map(([f, t]) => `${f}: ${showTy(t)}`).join("; ")} }`;
    case "union": return ty.variants.map((v) => showTy({ t: "record", fields: [[ty.key, v.tag], ...v.fields] })).join(" | ");
    case "array": { const s = showTy(ty.of); return s.includes(" ") && !s.startsWith("{") ? `(${s})[]` : `${s}[]`; }
    case "map": return `Map<string, ${showTy(ty.of)}>`;
  }
}

/** A value of the type, written as a JavaScript expression, to start from. */
export function sample(ty: Ty, depth = 0): string {
  switch (ty.t) {
    case "bool": return "true";
    case "bigint": return "3n";
    case "number": return depth === 0 ? "7" : String(3 + depth);
    case "string": return depth === 0 ? '"alice"' : '"bob"';
    case "tag": return "bool" in ty && ty.bool !== undefined ? String(ty.bool) : quote(ty.value ?? []);
    case "lits": return quote(ty.values[ty.values.length > 1 ? 1 : 0]);
    case "option": return sample(ty.of, depth);
    case "record": return `{ ${ty.fields.map(([f, t]) => `${f}: ${sample(t, depth + 1)}`).join(", ")} }`;
    case "union": { const v = ty.variants[0]; return sample({ t: "record", fields: [[ty.key, v.tag], ...v.fields] }, depth); }
    case "array": return `[${sample(ty.of, depth + 1)}, ${sample(ty.of, depth + 2)}]`;
    case "map": return `new Map([["alice", ${sample(ty.of, depth + 1)}]])`;
  }
}

/** Why the model stopped, in words, for a fault observation (`["error", …]`). */
export function faultText(message: string): { outside: boolean; text: string } {
  if (message === "timeout") return { outside: true, text: "The model ran out of steps (fuel). A loop that may not end is outside its claim." };
  if (message.startsWith("unsupported:")) {
    const what = message.slice("unsupported:".length).trim();
    return { outside: true, text: `This run leaves what the model covers (${what}). The function's safety condition is false on these arguments, so the theorem claims nothing about them.` };
  }
  return { outside: false, text: message };
}
