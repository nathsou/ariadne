// Bundles the playground into `dist/`: the page, its scripts and styles (fonts included), the workers,
// and `public/` (the translator's WebAssembly, `../wasm/build.sh`, and the examples' data, `../data.mjs`).
// Everything is served from the same origin: no CDN.
import { cpSync, mkdirSync, readFileSync, rmSync, watch, writeFileSync } from "node:fs";
import { join } from "node:path";

const here = import.meta.dir;
const out = join(here, "dist");

async function build() {
  rmSync(out, { recursive: true, force: true });
  mkdirSync(out, { recursive: true });
  const result = await Bun.build({
    entrypoints: ["src/main.ts", "src/translator.worker.ts", "src/js.worker.ts"].map((e) => join(here, e)),
    outdir: out,
    naming: { entry: "[name].[ext]", asset: "assets/[name]-[hash].[ext]", chunk: "[name]-[hash].[ext]" },
    target: "browser",
    format: "esm",
    minify: true,
    sourcemap: "linked",
  });
  if (!result.success) {
    for (const log of result.logs) console.error(log);
    throw new Error("build failed");
  }
  cpSync(join(here, "public"), out, { recursive: true });
  // The fonts' stylesheets and files as published: with unicode-range, a browser fetches only the
  // subsets a page uses.
  for (const font of ["inter", "jetbrains-mono"]) {
    const from = join(here, "node_modules/@fontsource-variable", font);
    cpSync(join(from, "index.css"), join(out, "fonts", font, "index.css"));
    cpSync(join(from, "files"), join(out, "fonts", font, "files"), { recursive: true, filter: (f) => !f.endsWith(".woff") });
  }
  const version = Date.now().toString(36);
  const html = readFileSync(join(here, "index.html"), "utf8").replaceAll("%VERSION%", version);
  writeFileSync(join(out, "index.html"), html);
  writeFileSync(join(out, ".nojekyll"), "");
  console.log(`built ${out}`);
}

await build();
if (process.argv.includes("--watch")) {
  let timer: ReturnType<typeof setTimeout> | undefined;
  watch(join(here, "src"), { recursive: true }, () => {
    clearTimeout(timer);
    timer = setTimeout(() => build().catch((e) => console.error(e)), 100);
  });
  const server = Bun.serve({
    port: 4173,
    fetch(req) {
      let path = new URL(req.url).pathname;
      if (path.endsWith("/")) path += "index.html";
      const file = Bun.file(join(out, path));
      return new Response(file);
    },
  });
  console.log(`serving on http://localhost:${server.port}`);
}
