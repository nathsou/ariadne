// Shapes of what the translator (Web.lean), the extraction tool (Extract.lean) and data.mjs produce.

/** A type as `ariadne signatures` describes it. */
export type Ty =
  | { t: "bool" } | { t: "bigint" } | { t: "number" } | { t: "string" }
  | { t: "tag"; value?: number[]; bool?: boolean }
  | { t: "lits"; values: number[][] }
  | { t: "option"; nullish: "undef" | "null" | "both"; of: Ty }
  | { t: "record"; fields: [string, Ty][] }
  | { t: "union"; key: string; variants: { tag: Ty; fields: [string, Ty][] }[] }
  | { t: "array"; of: Ty }
  | { t: "map"; of: Ty };

export interface Signature {
  name: string;
  exported: boolean;
  class: string | null;
  method: boolean;
  void: boolean;
  params: Ty[];
  result: Ty;
}

/** What the checker logged about a span of the source (UTF-8 byte offsets). */
export interface Hover {
  start: number;
  stop: number;
  kind: "expr" | "var" | "function" | "method";
  ts: string;
  lean: string;
  name?: string;
  term?: string;
  safe?: string;
  params?: { name: string; ts: string; lean: string }[];
}

export interface Diagnostic {
  code: string;
  message: string;
  startByte: number;
  endByte: number;
  line: number;
  column: number;
  notes: string[];
  help: string | null;
  related: { startByte: number; endByte: number; message: string }[];
}

export type Translation =
  | { ok: true; lean: string; signatures: Signature[]; validators: string | null; hovers: Hover[]; ms: number }
  | { ok: false; diagnostic: Diagnostic; hovers: Hover[]; ms: number };

/** A JavaScript value as the model and `scripts/observe.mjs` describe it. */
export type Obs = [string, ...unknown[]];

/** Positions from Lean: 1-based line, 0-based column in code points. */
export type LeanPos = [number, number];

export interface LeanHover { start: LeanPos; stop: LeanPos; name: string; kind: "const" | "local"; type?: string }
export interface LeanGoal { start: LeanPos; stop: LeanPos; before: string[]; after: string[] }
export interface LeanTheorem { name: string; line: number; statement: string; axioms: string[]; doc?: string; module: string }
export interface LeanInfo {
  hovers: LeanHover[];
  goals: LeanGoal[];
  theorems: LeanTheorem[];
  consts: Record<string, { signature: string; doc?: string }>;
  messages: { severity: string; pos: LeanPos; text: string }[];
}

export interface ExampleMeta {
  slug: string;
  title: string;
  size: string;
  summary: string;
  source: string;
  namespace: string;
  theorems: number;
  lines: number;
}

export interface ExampleData extends ExampleMeta {
  path: string;
  source: string;
  lean?: { path: string; text: string; info: LeanInfo };
  proofs?: { path: string; text: string; info: LeanInfo };
}

export interface BuildInfo { version: string; commit: string; lean: string }
