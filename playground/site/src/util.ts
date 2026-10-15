// DOM and text helpers.

type Child = Node | string | null | undefined | false;
type Attrs = Record<string, unknown> & { class?: string; style?: string };

/** `h("div", { class: "x", onclick }, child...)`: an element. */
export function h<K extends keyof HTMLElementTagNameMap>(tag: K, attrs: Attrs | null = null, ...children: (Child | Child[])[]) {
  const node = document.createElement(tag);
  for (const [key, value] of Object.entries(attrs ?? {})) {
    if (value === undefined || value === null || value === false) continue;
    if (key.startsWith("on") && typeof value === "function") node.addEventListener(key.slice(2), value as EventListener);
    else if (key === "class") node.className = String(value);
    else if (key === "html") node.innerHTML = String(value);
    else if (value === true) node.setAttribute(key, "");
    else node.setAttribute(key, String(value));
  }
  for (const child of children.flat()) {
    if (child === null || child === undefined || child === false) continue;
    node.append(child);
  }
  return node;
}

const icons: Record<string, string> = {
  chevron: '<path d="m4 6 4 4 4-4"/>',
  check: '<path d="m3.5 8.5 3 3 6-7"/>',
  x: '<path d="m4 4 8 8M12 4l-8 8"/>',
  alert: '<path d="M8 2.5 14.5 13.5h-13z"/><path d="M8 6.5v3M8 11.6v.1"/>',
  info: '<circle cx="8" cy="8" r="6.2"/><path d="M8 7.2v4M8 4.9v.1"/>',
  share: '<path d="M6.5 9.5 9.5 6.5"/><path d="M8.6 4.3l1.3-1.3a2.7 2.7 0 0 1 3.8 3.8l-1.3 1.3M7.4 11.7 6.1 13a2.7 2.7 0 0 1-3.8-3.8l1.3-1.3"/>',
  sun: '<circle cx="8" cy="8" r="3"/><path d="M8 1.5v1.5M8 13v1.5M1.5 8H3M13 8h1.5M3.4 3.4l1 1M11.6 11.6l1 1M3.4 12.6l1-1M11.6 4.4l1-1"/>',
  moon: '<path d="M13.2 9.6A5.6 5.6 0 0 1 6.4 2.8a5.6 5.6 0 1 0 6.8 6.8z"/>',
  github: '<path d="M8 1.6a6.4 6.4 0 0 0-2 12.5c.3 0 .4-.1.4-.3v-1.2c-1.8.4-2.2-.8-2.2-.8-.3-.7-.7-.9-.7-.9-.6-.4 0-.4 0-.4.6 0 1 .7 1 .7.6 1 1.5.7 1.9.5 0-.4.2-.7.4-.9-1.4-.2-2.9-.7-2.9-3.2 0-.7.3-1.3.7-1.7-.1-.2-.3-.8.1-1.7 0 0 .5-.2 1.8.7a6 6 0 0 1 3.2 0c1.2-.8 1.8-.7 1.8-.7.3.9.1 1.5.1 1.7.4.4.7 1 .7 1.7 0 2.5-1.5 3-2.9 3.2.2.2.4.6.4 1.2v1.8c0 .2.1.4.4.3A6.4 6.4 0 0 0 8 1.6z" fill="currentColor" stroke="none"/>',
  book: '<path d="M2.5 3.5c2-.8 3.8-.6 5.5.8 1.7-1.4 3.5-1.6 5.5-.8v9c-2-.8-3.8-.6-5.5.8-1.7-1.4-3.5-1.6-5.5-.8z"/><path d="M8 4.3v9"/>',
  play: '<path d="M5 3.5v9l7-4.5z" fill="currentColor"/>',
  dice: '<rect x="2.5" y="2.5" width="11" height="11" rx="2.5"/><circle cx="5.7" cy="5.7" r=".9" fill="currentColor"/><circle cx="10.3" cy="10.3" r=".9" fill="currentColor"/><circle cx="8" cy="8" r=".9" fill="currentColor"/>',
  reset: '<path d="M3 8a5 5 0 1 0 1.5-3.6"/><path d="M3 2.5V5h2.5"/>',
  copy: '<rect x="5.5" y="5.5" width="8" height="8" rx="1.5"/><path d="M10.5 5.5V3.8c0-.7-.6-1.3-1.3-1.3H3.8c-.7 0-1.3.6-1.3 1.3v5.4c0 .7.6 1.3 1.3 1.3h1.7"/>',
  download: '<path d="M8 2.5v8M4.5 7 8 10.5 11.5 7M3 13.5h10"/>',
  expand: '<path d="M3 6V3h3M13 6V3h-3M3 10v3h3M13 10v3h-3"/>',
  collapse: '<path d="M6 3v3H3M10 3v3h3M6 13v-3H3M10 13v-3h3"/>',
  shield: '<path d="M8 1.8 13 3.6v4c0 3.1-2.1 5.4-5 6.6-2.9-1.2-5-3.5-5-6.6v-4z"/><path d="m5.7 8 1.6 1.6 3-3.2"/>',
  wand: '<path d="m2.5 13.5 8-8M9 3l.5-1.5L10 3l1.5.5L10 4l-.5 1.5L9 4l-1.5-.5zM12.5 7.5l.3-1 .3 1 1 .3-1 .3-.3 1-.3-1-1-.3z"/>',
  lean: '<path d="M2.5 13 6 3M6 3h7.5M6 8h5"/>',
  layers: '<path d="m8 2 6 3.2-6 3.2-6-3.2z"/><path d="m2 8.4 6 3.2 6-3.2M2 11.4l6 3.2 6-3.2"/>',
  sparkle: '<path d="M8 1.8l1.4 4.8 4.8 1.4-4.8 1.4L8 14.2l-1.4-4.8L1.8 8l4.8-1.4z"/>',
  fold: '<path d="M4 6h8M4 10h8"/><path d="M6.5 3.5 8 2l1.5 1.5M6.5 12.5 8 14l1.5-1.5"/>',
  terminal: '<rect x="1.8" y="2.5" width="12.4" height="11" rx="2"/><path d="m4.5 6.5 2 1.8-2 1.8M8.5 10.5h3"/>',
};

/** An inline SVG icon. */
export function icon(name: keyof typeof icons | string): SVGSVGElement {
  const wrap = document.createElement("span");
  wrap.innerHTML = `<svg viewBox="0 0 16 16" width="16" height="16" fill="none" stroke="currentColor" stroke-width="1.5" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true">${icons[name] ?? ""}</svg>`;
  return wrap.firstChild as SVGSVGElement;
}

/** UTF-8 byte offsets of `text` to UTF-16 offsets (the editor's). */
export function byteMapper(text: string): (byte: number) => number {
  const table: number[] = [];
  let bytes = 0;
  for (let i = 0; i < text.length; i++) {
    const c = text.codePointAt(i)!;
    const n = c < 0x80 ? 1 : c < 0x800 ? 2 : c < 0x10000 ? 3 : 4;
    for (let k = 0; k < n; k++) table[bytes + k] = i;
    bytes += n;
    if (c >= 0x10000) i++;
  }
  table[bytes] = text.length;
  return (byte) => table[Math.min(byte, bytes)] ?? text.length;
}

/** UTF-16 offsets of Lean positions (1-based lines, code point columns) in `text`. */
export function leanPosMapper(text: string): (pos: [number, number]) => number {
  const starts = [0];
  for (let i = 0; i < text.length; i++) if (text[i] === "\n") starts.push(i + 1);
  return ([line, col]) => {
    let i = starts[line - 1] ?? text.length;
    for (let c = 0; c < col && i < text.length && text[i] !== "\n"; c++) i += (text.codePointAt(i)! >= 0x10000 ? 2 : 1);
    return i;
  };
}

/** `node.replaceChildren(...)`, skipping absent children (the DOM would print them as "null"). */
export function fill(node: Element, ...children: (Node | string | null | undefined | false)[]) {
  node.replaceChildren(...children.filter((c): c is Node | string => c !== null && c !== undefined && c !== false));
}

export function toast(message: string) {
  document.querySelector(".toast")?.remove();
  const t = h("div", { class: "toast", role: "status" }, message);
  document.body.append(t);
  setTimeout(() => t.remove(), 2200);
}

export function debounce<A extends unknown[]>(f: (...a: A) => void, ms: number) {
  let timer: ReturnType<typeof setTimeout> | undefined;
  return (...a: A) => {
    clearTimeout(timer);
    timer = setTimeout(() => f(...a), ms);
  };
}

export const storage = {
  get(key: string): string | null {
    try { return localStorage.getItem(key); } catch { return null; }
  },
  set(key: string, value: string) {
    try { localStorage.setItem(key, value); } catch {}
  },
  remove(key: string) {
    try { localStorage.removeItem(key); } catch {}
  },
};

/** The text of a string's UTF-16 code units, as the model stores strings. */
export const fromUnits = (units: number[]) => String.fromCharCode(...units);

export function escapeHtml(s: string) {
  return s.replace(/[&<>"']/g, (c) => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" })[c]!);
}

export async function copyText(text: string) {
  try {
    await navigator.clipboard.writeText(text);
    return true;
  } catch {
    return false;
  }
}

export function download(name: string, text: string) {
  const url = URL.createObjectURL(new Blob([text], { type: "text/plain" }));
  const a = h("a", { href: url, download: name });
  document.body.append(a);
  a.click();
  a.remove();
  setTimeout(() => URL.revokeObjectURL(url), 1000);
}
