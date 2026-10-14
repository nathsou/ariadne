# Playground

A static page, deployed to GitHub Pages by `.github/workflows/pages.yml`, where Ariadne runs in the
browser: <https://nathsou.github.io/ariadne/>.

- **Translate as you type.** The translator (`Ariadne.Front`) is compiled to WebAssembly and runs in a
  worker. Hovering the TypeScript shows what each expression, variable and function denotes: its Lean
  type, its readable Lean term, its safety condition (the checker's log, `translateLogged`).
- **Refusals, explained.** A program outside the subset gets the diagnostic, an explanation of why the
  subset draws the line there, a rewrite (applied in one click when it is mechanical), and a link into
  `docs/LANGUAGE.md`, which the page renders.
- **Run.** Each call runs in Ariadne's model of JavaScript (the trusted base, compiled to WebAssembly) and
  as the real JavaScript in the browser, side by side; classes run as sessions of method calls; the random
  test is `scripts/differential.mjs` in the browser. Arguments are checked with the generated validators.
- **Proofs.** Each example's proofs, kernel-checked in CI, with each tactic's goals and every name's type,
  recorded by `lake exe extract` when CI elaborates them (the page cannot run Lean, so these stay those of
  the example as written).

## Layout

| Path | What |
| --- | --- |
| `Web.lean` | The translator's entry points for the page: translate, and run a call in the model (JSON in and out) |
| `wasm/` | `build.sh` compiles Lean's runtime, the standard library modules the translator imports and Ariadne's front end to WebAssembly; `glue.c` is the C interface |
| `examples/*.ts`, `examples.json` | The examples: their source, and which generated file and proofs go with each (drive's kernel comes from `Tests/`) |
| `Examples/` | The examples' translations (generated, checked in) and their proofs |
| `Extract.lean` | `lake exe extract`: elaborates a Lean file and records its hovers, goals, theorems and axioms |
| `data.mjs` | Checks that each translation is current, and writes the page's data (`site/public/data/`) |
| `site/` | The page: TypeScript, CodeMirror, bundled by Bun with everything it loads (no CDN) |

## Build

With Lean (the pinned toolchain), Bun, CMake and [Emscripten](https://emscripten.org) 6.0.12 on `PATH`:

```sh
playground/build.sh                  # everything, into playground/site/dist
cd playground/site && bun run dev    # rebuild the page on change, serve it on localhost:4173
```

The first WebAssembly build generates and compiles the standard library's C (a few minutes); later
builds reuse it from `playground/.build`.

Lean has no WebAssembly release, so `wasm/build.sh` builds what the translator needs: Lean's runtime from
the Lean sources at the toolchain's tag, single-threaded (a static page cannot have the cross-origin
isolation that WebAssembly threads need), and the C of the standard library modules it imports, which the
toolchain's own `lean` generates from the sources it ships. Lean emits portable C, so the 64-bit host's
output compiles for wasm32; the translations it produces are byte-for-byte those of the native build
(`data.mjs` compares the examples' with the checked-in files the native translator wrote).

## Adding an example

1. Write `examples/name.ts`, and add it to `examples.json` (with a namespace `Examples.Name`, and
   optionally `try`: arguments the Run tab starts with, and for a class `@Class`, a scenario of calls).
2. Translate it: `../.lake/build/bin/ariadne translate examples/name.ts --out Examples/Name.lean --namespace Examples.Name`.
3. Prove things in `Examples/Name/Proofs.lean`, import it from `Examples.lean`, and `lake build Examples`.
