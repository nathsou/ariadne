// What a diagnostic means, why the subset draws the line there, and how to rewrite the code: shown
// under the editor when the translator refuses a program. Several refusals share a message ("this
// statement is outside the supported subset"), so the explanation also reads the code it points at.

export interface Edit { from: number; to: number; insert: string }

export interface Explanation {
  title: string;
  why: string;
  before?: string;
  after?: string;
  /** An edit that applies the rewrite, when it is mechanical. */
  fix?: Edit;
  /** Text to find in the subset guide (a row of its "Refused" table, or a heading). */
  guide?: string;
}

interface Context {
  code: string;
  message: string;
  /** The source the diagnostic points at, and its offsets in the whole source (UTF-16). */
  snippet: string;
  from: number;
  to: number;
  source: string;
}

type Rule = (c: Context) => Explanation | null;

const id = String.raw`[A-Za-z_$][\w$]*`;

const rules: Rule[] = [
  // In-place changes of arrays and records.
  (c) => {
    const m = c.snippet.match(new RegExp(String.raw`^(${id}(?:\.${id})*)\.push\(([\s\S]*)\)(;?)$`));
    if (!m) return null;
    const insert = `${m[1]} = [...${m[1]}, ${m[2]}]${m[3]}`;
    return {
      title: "Arrays are values: push has nothing to change",
      why: "In Ariadne's model, arrays and records are values, like numbers: nothing can change one in place, so nothing two parts of the code share can change under them. Build the new array and assign it instead. (A parameter or a let can be reassigned.)",
      before: c.snippet, after: insert, fix: { from: c.from, to: c.to, insert }, guide: "push",
    };
  },
  (c) => {
    const m = c.snippet.match(new RegExp(String.raw`^(${id})\[([^\]]+)\]\s*=\s*([\s\S]+?);?$`));
    if (!m) return null;
    return {
      title: "Arrays are values: an element cannot be assigned",
      why: "Arrays are values in the model, so `xs[i] = v` has no meaning there. Build the array you want: with a spread to add, or with a loop over `entries()` to replace an element.",
      before: c.snippet,
      after: `let next: T[] = [];\nfor (const [j, x] of ${m[1]}.entries()) {\n  next = [...next, j === ${m[2]} ? ${m[3]} : x];\n}\n${m[1]} = next;`,
      guide: "push",
    };
  },
  (c) => {
    const m = c.snippet.match(new RegExp(String.raw`^(${id})\.(${id})\s*=\s*([\s\S]+?)(;?)$`));
    if (!m || m[1] === "this") return null;
    const insert = `${m[1]} = { ...${m[1]}, ${m[2]}: ${m[3]} }${m[4]}`;
    return {
      title: "Records are values: a field cannot be assigned",
      why: "Records are values in the model, like numbers. Make a copy with the field changed: `{ ...r, f: v }` is in the subset.",
      before: c.snippet, after: insert, fix: { from: c.from, to: c.to, insert }, guide: "push",
    };
  },
  (c) => {
    if (!/array method 'sort'/.test(c.message)) return null;
    const insert = c.snippet.replace(/\.sort\(/, ".toSorted(");
    return {
      title: "sort changes the array: use toSorted",
      why: "`sort` reorders its array in place, and arrays are values in the model. `toSorted` returns the sorted copy, and is in the subset. Its safety condition asks that the comparator be consistent, which the `cmp_laws` tactic proves for comparators written as a chain of keys.",
      before: c.snippet, after: insert, fix: insert !== c.snippet ? { from: c.from, to: c.to, insert } : undefined, guide: "toSorted",
    };
  },
  (c) => {
    const m = c.snippet.match(/^for\s*\(\s*let\s/);
    if (!m) return null;
    const insert = c.snippet.replace(/^for\s*\(\s*let\s/, "for (const ");
    return {
      title: "Loop variables are const",
      why: "`for (const x of xs)` is in the subset; a loop variable cannot be reassigned, which keeps loops and narrowing sound.",
      before: c.snippet.split("\n")[0], after: insert.split("\n")[0], fix: { from: c.from, to: c.to, insert }, guide: "loop variable",
    };
  },
  (c) => {
    if (!/^(this statement|this expression) is outside/.test(c.message)) return null;
    if (/^\s*throw\b/.test(c.snippet)) return { title: "throw is not modeled yet", why: "Exceptions are not in the model yet. Return a value that says what went wrong (a union with a tag, or undefined).", guide: "throw" };
    if (/^\s*try\b/.test(c.snippet)) return { title: "try is not modeled yet", why: "Exceptions are not in the model yet.", guide: "throw" };
    if (/=>\s*\{/.test(c.snippet) || /function\s*\(/.test(c.snippet)) {
      return {
        title: "Callbacks have an expression body",
        why: "A callback (to map, filter, some, every, find or toSorted) is an arrow with an expression body, or a function declared earlier: a callback may not assign or declare variables.",
        before: "xs.map((x) => {\n  return x + 1;\n})", after: "xs.map((x) => x + 1)", guide: "Block-bodied arrows",
      };
    }
    return null;
  },
  (c) => /callback other than an arrow/.test(c.message) ? {
    title: "Callbacks take one parameter and have an expression body",
    why: "Callbacks are arrows with an expression body and at most one parameter (no index), or declared functions. For the index, loop over `xs.entries()`.",
    before: "xs.map((x, i) => x * i)", after: "let out: number[] = [];\nfor (const [i, x] of xs.entries()) {\n  out = [...out, x * i];\n}", guide: "Block-bodied arrows",
  } : null,
  (c) => /non-integer number literal/.test(c.message) ? {
    title: "Numbers are integers",
    why: "In the subset, `number` means a safe integer: binary64 arithmetic is exact there, so the Lean side is plain `Int`. Count in smaller units (cents, milliseconds), or use bigint.",
    guide: "Non-integer literals",
  } : null,
  (c) => /outside the safe integer range/.test(c.message) ? {
    title: "Number literals stay within ±(2^53 − 1)",
    why: "Past 2^53, binary64 numbers skip integers, so the model's numbers stop there. For larger values, use bigint (`9007199254740993n`), which the model treats exactly.",
    guide: "Non-integer literals",
  } : null,
  (c) => /^'do'/.test(c.message) ? {
    title: "do … while is not in the subset",
    why: "Use a while loop, running the body once before it if needed. (A do-while condition's safety would join the loop's.)",
    guide: "do … while",
  } : null,
  (c) => /^'\*\*'/.test(c.message) ? {
    title: "No ** (numbers are integers)",
    why: "Exponentiation can leave the integers (`2 ** -1`), and other `Math` functions too. Multiply in a loop, or use bigint.",
    guide: "**",
  } : null,
  (c) => /^this type is outside/.test(c.message) && /Map|Set/.test(c.snippet + c.source.slice(Math.max(0, c.from - 80), c.from)) ? {
    title: "Maps live in a class",
    why: "A Map is supported as a private field of a class (`private m = new Map<string, T>()`), changed through `this.m.set/delete` in void methods: the model then proves that changing the object in place is the same as computing a new state.",
    before: "const m = new Map<string, number>();", after: "class Index {\n  private m = new Map<string, number>();\n  // methods use this.m.get/has/set/delete\n}",
    guide: "Local `Map`",
  } : null,
  (c) => /while condition with number arithmetic/.test(c.message) ? {
    title: "A while condition compares; it does not compute",
    why: "The condition is evaluated at every iteration, and its safety would join the loop's. Keep arithmetic in the body: compare variables the body updates.",
    before: "while (i + 1 < n) { … }", after: "let next = i + 1;\nwhile (next < n) {\n  …\n  next = i + 1;\n}",
    guide: "while",
  } : null,
  (c) => /calls itself/.test(c.message) ? {
    title: "No recursion yet",
    why: "Functions call functions declared before them, and methods may not call themselves. Write the recursion as a loop (a while loop's safety condition then asks you to prove that it ends).",
    guide: "Recursion",
  } : null,
  (c) => /falls through/.test(c.message) ? {
    title: "A case falls into the next",
    why: "End each case with break, return or continue, or group labels that share a body (`case 'a': case 'b':`).",
    guide: "switch",
  } : null,
  (c) => /without a common literal field/.test(c.message) ? {
    title: "Unions need a tag",
    why: "A union of records is told apart by a field holding a literal (a discriminated union), which becomes the Lean constructor. Add one.",
    before: "type Shape = { r: number } | { w: number; h: number };",
    after: "type Shape = { kind: 'circle'; r: number } | { kind: 'rect'; w: number; h: number };",
    guide: "Unions of records",
  } : null,
  (c) => /a field other than a Map/.test(c.message) ? {
    title: "Class fields are Maps",
    why: "A class's state is its Map fields (`private f = new Map<string, T>()`), so methods change it through `this.f.set/delete`.",
    guide: "Classes",
  } : null,
  (c) => /named Math/.test(c.message) ? { title: "Math is JavaScript's", why: "`Math.floor` must be JavaScript's, so nothing may be named Math.", guide: "Math" } : null,
  (c) => {
    const m = c.message.match(/string method '(\w+)'/);
    return m ? {
      title: `The string method ${m[1]} is not in the subset`,
      why: "On strings: `length`, `startsWith`, `endsWith`, `includes`, `indexOf`, `slice` with one or two arguments, `+` and comparisons. (Strings are UTF-16 code units in the model, as in JavaScript.)",
      guide: "On strings",
    } : null;
  },
  (c) => {
    const m = c.message.match(/^'(===|!==)' on an? (optional|array|record)/);
    if (!m) return null;
    if (m[2] === "optional") {
      const eq = c.snippet.match(new RegExp(String.raw`^(${id})\s*(===|!==)\s*(undefined|null)$`));
      const insert = eq ? `${eq[1]} ${eq[2] === "===" ? "==" : "!="} null` : undefined;
      return {
        title: "Test an optional with == null",
        why: "`x == null` (or `x != null`) tests for both undefined and null, and narrows `x` to its type after the test: `if (x == null) return …;` leaves `x` defined for the rest of the block. To compare a defined value, narrow first.",
        before: eq ? c.snippet : "if (role === 'owner') …", after: insert ?? "if (role == null) return false;\nreturn role === 'owner';",
        fix: insert ? { from: c.from, to: c.to, insert } : undefined, guide: "== null",
      };
    }
    return {
      title: "Objects compare by identity",
      why: `\`===\` on ${m[2] === "array" ? "arrays" : "records"} compares references in JavaScript, which the model doesn't have: there, ${m[2]}s are values. Compare what identifies them (a key field), or their contents.`,
      guide: "`===` or `includes` on objects",
    };
  },
  (c) => /includes' on an array of a record/.test(c.message) ? {
    title: "includes compares objects by identity",
    why: "Use `some` with what identifies the record.",
    before: "items.includes(item)", after: "items.some((x) => x.id === item.id)", guide: "`===` or `includes` on objects",
  } : null,
  (c) => {
    if (!/^'\/' on numbers/.test(c.message)) return null;
    const insert = `Math.floor(${c.snippet})`;
    return {
      title: "Division gives fractions: floor it",
      why: "Numbers are integers in the subset, and `a / b` is not one. `Math.floor(a / b)` is, and denotes `Int.fdiv`; its safety condition asks for a divisor other than zero.",
      before: c.snippet, after: insert, fix: { from: c.from, to: c.to, insert }, guide: "Math.floor",
    };
  },
  (c) => {
    const m = c.message.match(/^'(\w+)' is not assignable \(a const declaration\)/);
    if (!m) return null;
    const decl = new RegExp(String.raw`\bconst\s+${m[1]}\b`).exec(c.source.slice(0, c.from));
    return {
      title: `${m[1]} is a const`,
      why: "Declare it with `let` to assign it. (Loop variables and a counted loop's index stay const: that keeps loops and narrowing sound.)",
      before: `const ${m[1]} = …`, after: `let ${m[1]} = …`,
      fix: decl ? { from: decl.index, to: decl.index + 5, insert: "let" } : undefined, guide: "Assigning a `const`",
    };
  },
  (c) => /the bound '\w+' must be a const/.test(c.message) ? {
    title: "A counted loop's bound is a const",
    why: "`for (let i = 0; i < n; i++)` needs `n` to be a const, so the loop's length is known when it starts.",
    before: "for (let i = 0; i < xs.length; i++)", after: "const n = xs.length;\nfor (let i = 0; i < n; i++)", guide: "counted loop",
  } : null,
  (c) => /needs an optional type here/.test(c.message) ? {
    title: "undefined needs an optional type",
    why: "Give the variable or parameter an optional type, `T | undefined`, so that undefined is one of its values.",
    guide: "Optionals",
  } : null,
  (c) => /^(bigint|number|string|boolean|a record|an array|a union|an optional|a Map|a string literal union) where .* is expected$/.test(c.message) ? {
    title: "The types don't match",
    why: "The checker found a value of one type where another is expected. number and bigint don't mix (as in TypeScript); a string is not a string-literal union without a check.",
  } : null,
  (c) => /^no field '/.test(c.message) ? { title: "No such field", why: "The record type declares its fields; a literal may not add others, and a read must name one of them.", guide: "Records" } : null,
  (c) => /'this' used as a value/.test(c.message) ? {
    title: "this is not a value",
    why: "Methods use `this.f.get/has/size/set/delete` and call `this.m(…)`, but `this` itself cannot be stored, passed or returned: it would share the object's maps.",
    guide: "`this` other than",
  } : null,
  (c) => /only a method returning void may change the state|changes the state: call it as a statement/.test(c.message) ? {
    title: "State changes happen in void methods",
    why: "A method that changes the maps returns void and is called as a statement; a method returning a value may read the state but not change it. (The model proves that the object changing in place is the same as the methods computing new states.)",
    guide: "Classes",
  } : null,
  (c) => /values may be undefined/.test(c.message) ? { title: "Map values are never undefined", why: "`get` returns undefined for a missing key, so a map whose values may be undefined would be ambiguous.", guide: "Classes" } : null,
  (c) => /Object.prototype property/.test(c.message) ? { title: "That name is inherited", why: "A field named like an Object.prototype property (toString, constructor, …) would read the inherited one when absent. Rename it." } : null,
  (c) => /case label repeated|no variant tagged/.test(c.message) ? { title: "Check the case labels", why: "Each case of a switch on a union names one of its tags, once." , guide: "switch" } : null,
  (c) => /as a callback must take one parameter/.test(c.message) ? { title: "Callbacks take one parameter", why: "A declared function passed as a callback takes exactly one parameter.", guide: "Block-bodied arrows" } : null,
  (c) => /may finish without returning/.test(c.message) ? {
    title: "Every path returns",
    why: "The function can reach its end without a return. Add one at the end (or an else branch).",
  } : null,
  (c) => /break or continue outside/.test(c.message) ? { title: "break and continue belong in loops", why: "Use them inside a loop (or break in a switch)." } : null,
  (c) => {
    const m = c.message.match(/^'(\w+)' (shadows a declaration in scope|is declared twice)/);
    return m ? {
      title: `${m[1]} is already a name in scope`,
      why: "Names in scope must be distinct: the model resolves names when the code runs, so a shadowed name would make the readable definitions differ from what runs. Rename one of them.",
      guide: "Shadowing",
    } : null;
  },
  (c) => /is not a function declared earlier/.test(c.message) ? {
    title: "Call functions declared earlier",
    why: "A function can call the functions declared before it. Move the callee above the caller. (This rules out recursion, which is not modeled yet.)",
    guide: "Recursion",
  } : null,
  (c) => /^unknown variable/.test(c.message) ? { title: "Unknown name", why: "The name is not declared in scope at this point." } : null,
  (c) => /found '\+\+'|found '--'/.test(c.message) ? {
    title: "Increments are statements",
    why: "`x++` and `x--` are in the subset as statements on a variable; not inside expressions, and not as `++x`.",
    before: "const y = x++;", after: "const y = x;\nx++;", guide: "`++x`",
  } : null,
];

export function explain(c: Context): Explanation | null {
  for (const rule of rules) {
    const e = rule(c);
    if (e) return e;
  }
  return null;
}
