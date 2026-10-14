// L5/L6: a class whose state is private Maps, void methods that change it, value
// methods that read it.

interface Entry {
  at: number;
  s: string;
  tag?: string;
}

function newer(s: string, stamp: string): boolean {
  return s === '' || s < stamp;
}

export class Book {
  private items = new Map<string, Entry>();
  private names = new Map<string, string>();
  private counts = new Map<string, number>();

  put(k: string, e: Entry): void {
    const cur = this.items.get(k);
    if (cur != null) {
      if (!newer(cur.s, e.s)) return;
    }
    this.items.set(k, e);
    this.bump(k);
  }

  private bump(k: string): void {
    const c = this.counts.get(k);
    this.counts.set(k, c == null ? 1 : c + 1);
  }

  rename(k: string, n: string): void {
    this.names.set(k, n);
    if (!this.items.has(k)) this.items.set(k, { at: 0, s: '' });
  }

  drop(k: string): void {
    this.items.delete(k);
    this.names.delete(k);
  }

  touchAll(ks: string[]): void {
    for (const k of ks) this.bump(k);
  }

  get(k: string): Entry | undefined {
    return this.items.get(k);
  }

  count(): number {
    return this.items.size;
  }

  keys(): string[] {
    return [...this.items.keys()];
  }

  latest(): number {
    let best = 0;
    for (const e of [...this.items.values()]) {
      if (e.at > best) best = e.at;
    }
    return best;
  }

  nameOf(k: string): string {
    const n = this.names.get(k);
    return n == null ? k : n;
  }

  labels(): string[] {
    return [...this.names.keys()].map((k: string) => this.nameOf(k) + '!');
  }
}
