// The Subset tab: docs/LANGUAGE.md (copied at build time, so it is the release's), searchable, and
// reachable from a diagnostic's explanation.
import { marked } from "marked";
import { h, icon } from "./util";

export class SubsetView {
  el: HTMLElement;
  private doc = h("article", { class: "doc" });
  private search: HTMLInputElement;
  private scroller: HTMLElement;
  private loaded: Promise<void> | null = null;

  constructor(private load: () => Promise<string>) {
    this.search = h("input", { class: "field", type: "search", placeholder: "Filter: push, Map, while, ===, …", "aria-label": "Filter the subset guide",
      oninput: () => this.filter(this.search.value) }) as HTMLInputElement;
    this.scroller = h("div", { class: "scroll" },
      h("div", { class: "doc-search" }, icon("book"), this.search,
        h("a", { href: "https://github.com/nathsou/ariadne/blob/main/docs/LANGUAGE.md", target: "_blank", rel: "noopener", class: "hide-narrow" }, "docs/LANGUAGE.md")),
      this.doc);
    this.el = h("div", { class: "view" }, this.scroller);
  }

  ensure() {
    this.loaded ??= this.render();
    return this.loaded;
  }

  private async render() {
    this.doc.innerHTML = marked.parse(await this.load(), { async: false }) as string;
    for (const a of this.doc.querySelectorAll("a[href]")) {
      const href = a.getAttribute("href")!;
      if (!/^https?:/.test(href)) a.setAttribute("href", new URL(href, "https://github.com/nathsou/ariadne/blob/main/docs/").href);
      a.setAttribute("target", "_blank");
    }
  }

  private filter(q: string) {
    const query = q.trim().toLowerCase();
    for (const node of this.doc.querySelectorAll("li, tr, p")) {
      if (node.closest("thead")) continue;
      node.classList.toggle("hidden-by-search", query !== "" && !node.textContent!.toLowerCase().includes(query));
    }
  }

  /** Scroll to the first row or item mentioning `text`, and flash it. */
  async focus(text: string) {
    await this.ensure();
    this.search.value = "";
    this.filter("");
    const needle = text.toLowerCase().replace(/`/g, "");
    const nodes = [...this.doc.querySelectorAll("tr, li, h2, h3, p")];
    const target = nodes.find((n) => n.textContent!.toLowerCase().replace(/`/g, "").includes(needle));
    if (!target) return;
    requestAnimationFrame(() => target.scrollIntoView({ block: "center", behavior: "smooth" }));
    const row = target;
    row.classList.remove("flash");
    void (row as HTMLElement).offsetWidth;
    row.classList.add("flash");
    if (row.tagName !== "TR") {
      (row as HTMLElement).style.transition = "background 2s";
      (row as HTMLElement).style.background = "var(--thread-soft)";
      setTimeout(() => { (row as HTMLElement).style.background = ""; }, 1200);
    }
  }
}
