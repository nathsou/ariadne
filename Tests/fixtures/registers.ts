// drive core/kernel/registers.ts (nathsou/drive 1e41c79), unchanged.
// The index's registers: where each stored object is and its deletion marks, the packs, the usage counters and the
// albums. Each is last-writer-wins (or first-writer-wins) by hybrid-logical-clock stamp, so operations converge in any
// order; IndexState (core/index/state.ts) hands those operations here, and the file tree's to tree.ts.
//
// Part of the verified kernel (docs/VERIFIED_KERNEL.md): written in its subset, translated to Lean
// (verify/Drive/Kernel/Registers.lean), printed back and run against it. The maps are owned (private, never handed out,
// iterated only as copies) and the records in them are replaced, never changed, so the Lean translation passes the state
// along instead of sharing it.
// Nested maps are flattened to composite keys (`ref\0provider`): object ids never contain `\0`, and only the last part
// of a key can be any string.

/** Where an object is stored on a provider: the latest place or unplace (`s`), and the newest unplace ever seen (`u`). */
export interface Placed {
  p: string;
  cls: string;
  at: number;
  s: string;
  gone: boolean;
  u?: string;
}

/** A deletion mark of an object on a provider (`on`), waiting out the provider's undo window, or its removal. */
export interface Mark {
  ref: string;
  p: string;
  since: number;
  s: string;
  on: boolean;
  reason?: string;
}

/** A pack of renditions; the earliest description wins. */
export interface Pack {
  id: string;
  size: number;
  csize: number;
  at: number;
  s?: string;
  hn?: string;
}

/** Requests and bytes counted against a provider. */
export interface Counters {
  put: number;
  get: number;
  list: number;
  head: number;
  delete: number;
  copy: number;
  restore: number;
  ingress: number;
  egress: number;
}

/** A device's running total for a provider and month: the highest per counter wins. */
export interface Total {
  p: string;
  month: string;
  device: string;
  c: Counters;
}

/** Increments for a provider and month, from usage operations of earlier versions (without `total`). */
export interface Increments {
  p: string;
  month: string;
  c: Counters;
}

/** A provider and month with usage, and the devices with a running total for it. */
export interface Period {
  p: string;
  month: string;
  devices: string[];
}

/** The usage of a provider in a month. */
export interface Usage {
  p: string;
  month: string;
  c: Counters;
}

/** An album: its name and cover (latest wins, `nameS` and `coverS` are their stamps) and its deletion (earliest wins). */
export interface AlbumRec {
  id: string;
  name: string;
  created: number;
  cover?: string;
  deleted?: string;
  nameS?: string;
  coverS?: string;
}

/** Whether a node is in an album (latest add or remove wins). */
export interface AlbumItem {
  aid: string;
  id: string;
  s: string;
  present: boolean;
}

function key(a: string, b: string): string {
  return a + '\0' + b;
}

/** JavaScript's string order, for lists kept sorted: they then don't depend on the order operations arrived in. */
function byString(a: string, b: string): number {
  return a < b ? -1 : b < a ? 1 : 0;
}

/** Whether a write at `stamp` replaces a register written at `s` (an absent or empty stamp: never written). */
function newer(s: string | undefined, stamp: string): boolean {
  if (s == null) return true;
  return s === '' || s < stamp;
}

/** Whether a first-writer-wins register written at `s` takes a write at `stamp` (an earlier one). */
function earlier(s: string | undefined, stamp: string): boolean {
  if (s == null) return true;
  return s === '' || stamp < s;
}

/** The newer of a stamp that may be absent and another. */
function newest(s: string | undefined, stamp: string): string {
  if (s == null) return stamp;
  return s === '' || s < stamp ? stamp : s;
}

/** Whether `stamp` comes before `s` (never when `s` is absent or empty). */
function before(stamp: string, s: string | undefined): boolean {
  if (s == null) return false;
  return s !== '' && stamp < s;
}

function given(s: string | undefined): boolean {
  return s == null ? false : true;
}

function otherwise(s: string | undefined, fallback: string): string {
  return s == null ? fallback : s;
}

/** Whether a pack described at `stamp` (whose time is `at`) loses to the description it has. */
function described(cur: Pack | undefined, stamp: string, at: number): boolean {
  if (cur == null) return false;
  const s = cur.s;
  if (s == null) return cur.at <= at;
  return s === '' ? cur.at <= at : !(stamp < s);
}

function larger(a: number, b: number): number {
  return a > b ? a : b;
}

export function zero(): Counters {
  return { put: 0, get: 0, list: 0, head: 0, delete: 0, copy: 0, restore: 0, ingress: 0, egress: 0 };
}

function highest(a: Counters, b: Counters): Counters {
  return {
    put: larger(a.put, b.put),
    get: larger(a.get, b.get),
    list: larger(a.list, b.list),
    head: larger(a.head, b.head),
    delete: larger(a.delete, b.delete),
    copy: larger(a.copy, b.copy),
    restore: larger(a.restore, b.restore),
    ingress: larger(a.ingress, b.ingress),
    egress: larger(a.egress, b.egress),
  };
}

function sum(a: Counters, b: Counters): Counters {
  return {
    put: a.put + b.put,
    get: a.get + b.get,
    list: a.list + b.list,
    head: a.head + b.head,
    delete: a.delete + b.delete,
    copy: a.copy + b.copy,
    restore: a.restore + b.restore,
    ingress: a.ingress + b.ingress,
    egress: a.egress + b.egress,
  };
}

export class Registers {
  /** Placements by `ref\0provider`. */
  private placed = new Map<string, Placed>();
  /** The providers each object has a placement on, sorted. */
  private providers = new Map<string, string[]>();
  /** Deletion marks by `ref\0provider`. */
  private marks = new Map<string, Mark>();
  private packs = new Map<string, Pack>();
  /** Running totals by `provider\0month\0device`. */
  private totals = new Map<string, Total>();
  /** Increments by `provider\0month`. */
  private increments = new Map<string, Increments>();
  /** Providers and months with usage, by `provider\0month`. */
  private periods = new Map<string, Period>();
  private albums = new Map<string, AlbumRec>();
  /** Album items by `album\0node`. */
  private items = new Map<string, AlbumItem>();

  // ---- placements and deletion marks ----

  /**
   * A `place` (`placed`) or `unplace` of `ref` on `p` at `stamp`, whose time is `at`. The latest wins; deletion marks
   * made before the object was deleted there don't outlive it, in whatever order operations arrive.
   */
  place(ref: string, p: string, placed: boolean, cls: string, stamp: string, at: number): void {
    const cur = this.placed.get(key(ref, p));
    const seen = cur == null ? undefined : cur.u;
    const u: string | undefined = placed ? seen : newest(seen, stamp);
    this.dropMarkBefore(ref, p, u);
    if (!newer(cur == null ? undefined : cur.s, stamp)) {
      if (!placed) this.noteUnplace(ref, p, newest(seen, stamp));
      return;
    }
    if (placed) this.put(ref, p, { p, cls, at, s: stamp, gone: false, u });
    else this.put(ref, p, { p, cls: '', at, s: stamp, gone: true, u });
  }

  /** Records an unplace older than the entry's latest operation: the entry stays, its newest unplace moves. */
  private noteUnplace(ref: string, p: string, u: string): void {
    const cur = this.placed.get(key(ref, p));
    if (cur == null) return;
    this.placed.set(key(ref, p), { ...cur, u });
  }

  private put(ref: string, p: string, e: Placed): void {
    if (!this.placed.has(key(ref, p))) this.providers.set(ref, [...this.providersOf(ref), p].toSorted(byString));
    this.placed.set(key(ref, p), e);
  }

  private providersOf(ref: string): string[] {
    const ps = this.providers.get(ref);
    return ps == null ? [] : ps;
  }

  private dropMarkBefore(ref: string, p: string, u: string | undefined): void {
    if (u == null) return;
    const mark = this.marks.get(key(ref, p));
    if (mark == null) return;
    if (u === '' || u < mark.s) return;
    this.marks.delete(key(ref, p));
  }

  /** A deletion mark (`on`) of `ref` on `p`, or its removal; one older than the object's deletion there is ignored. */
  mark(ref: string, p: string, on: boolean, reason: string | undefined, stamp: string, at: number): void {
    const placed = this.placed.get(key(ref, p));
    if (before(stamp, placed == null ? undefined : placed.u)) return;
    const cur = this.marks.get(key(ref, p));
    if (!newer(cur == null ? undefined : cur.s, stamp)) return;
    this.marks.set(key(ref, p), { ref, p, since: at, s: stamp, on, reason });
  }

  /** The placements of `ref`, removed ones included, by provider. */
  placements(ref: string): Placed[] {
    let out: Placed[] = [];
    for (const p of this.providersOf(ref)) {
      const e = this.placed.get(key(ref, p));
      if (e == null) continue;
      out = [...out, e];
    }
    return out;
  }

  isPlaced(ref: string): boolean {
    return this.providers.has(ref);
  }

  placedRefs(): string[] {
    return [...this.providers.keys()];
  }

  markOf(ref: string, p: string): Mark | undefined {
    return this.marks.get(key(ref, p));
  }

  markList(): Mark[] {
    return [...this.marks.values()];
  }

  // ---- packs ----

  /** A pack's description: the earliest wins (a pack is described once; a second one only comes from a buggy writer). */
  pack(id: string, size: number, csize: number, stamp: string, at: number, hn: string | undefined): void {
    if (described(this.packs.get(id), stamp, at)) return;
    this.packs.set(id, { id, size, csize, at, s: stamp, hn });
  }

  packOf(id: string): Pack | undefined {
    return this.packs.get(id);
  }

  packList(): Pack[] {
    return [...this.packs.values()];
  }

  // ---- usage ----

  /** A device's running total for `p` in `month`: a log applied twice (or replayed) counts nothing twice. */
  total(p: string, month: string, device: string, c: Counters): void {
    const cur = this.totals.get(key(key(p, month), device));
    this.totals.set(key(key(p, month), device), { p, month, device, c: highest(cur == null ? zero() : cur.c, c) });
    this.track(p, month, device, true);
  }

  /** Increments for `p` in `month` from earlier versions: they add up. */
  add(p: string, month: string, c: Counters): void {
    const cur = this.increments.get(key(p, month));
    this.increments.set(key(p, month), { p, month, c: sum(cur == null ? zero() : cur.c, c) });
    this.track(p, month, '', false);
  }

  private track(p: string, month: string, device: string, total: boolean): void {
    const cur = this.periods.get(key(p, month));
    const devices: string[] = cur == null ? [] : cur.devices;
    if (total && !devices.includes(device)) this.periods.set(key(p, month), { p, month, devices: [...devices, device].toSorted(byString) });
    else if (!this.periods.has(key(p, month))) this.periods.set(key(p, month), { p, month, devices });
  }

  /** A device's running total for `p` in `month` (what its next usage operation adds to). */
  totalOf(p: string, month: string, device: string): Counters {
    const t = this.totals.get(key(key(p, month), device));
    return t == null ? zero() : t.c;
  }

  /** The usage of `p` in `month`: the increments plus every device's running total. */
  usageOf(p: string, month: string): Counters {
    const inc = this.increments.get(key(p, month));
    let out = inc == null ? zero() : inc.c;
    const period = this.periods.get(key(p, month));
    if (period == null) return out;
    for (const d of period.devices) {
      const t = this.totals.get(key(key(p, month), d));
      if (t == null) continue;
      out = sum(out, t.c);
    }
    return out;
  }

  usageList(): Usage[] {
    return [...this.periods.values()].map((x) => ({ p: x.p, month: x.month, c: this.usageOf(x.p, x.month) }));
  }

  totalList(): Total[] {
    return [...this.totals.values()];
  }

  // ---- albums ----

  /** An `album` operation: a name and a cover (the latest wins), a deletion (the earliest wins). */
  album(aid: string, stamp: string, at: number, name: string | undefined, cover: string | undefined, deleted: boolean): void {
    this.touchAlbum(aid, at);
    const a = this.albums.get(aid);
    if (a == null) return;
    const renamed = given(name) && newer(a.nameS, stamp);
    const covered = given(cover) && newer(a.coverS, stamp);
    this.albums.set(aid, {
      ...a,
      name: renamed ? otherwise(name, a.name) : a.name,
      nameS: renamed ? stamp : a.nameS,
      cover: covered ? cover : a.cover,
      coverS: covered ? stamp : a.coverS,
      deleted: deleted && earlier(a.deleted, stamp) ? stamp : a.deleted,
    });
  }

  /** An `albumItems` operation: per node, the latest add or remove wins. */
  albumItems(aid: string, stamp: string, at: number, add: string[], remove: string[]): void {
    this.touchAlbum(aid, at);
    for (const id of add) this.item(aid, id, stamp, true);
    for (const id of remove) this.item(aid, id, stamp, false);
  }

  /** An album is created by its first operation, at the earliest time any of them has. */
  private touchAlbum(aid: string, at: number): void {
    const a = this.albums.get(aid);
    this.albums.set(aid, a == null ? { id: aid, name: 'Untitled album', created: at } : at < a.created ? { ...a, created: at } : a);
  }

  private item(aid: string, id: string, stamp: string, present: boolean): void {
    const cur = this.items.get(key(aid, id));
    if (newer(cur == null ? undefined : cur.s, stamp)) this.items.set(key(aid, id), { aid, id, s: stamp, present });
  }

  albumList(): AlbumRec[] {
    return [...this.albums.values()];
  }

  itemList(): AlbumItem[] {
    return [...this.items.values()];
  }

  // ---- snapshots: records as a snapshot holds them ----

  loadPlacement(ref: string, e: Placed): void {
    this.put(ref, e.p, e);
  }

  loadMark(m: Mark): void {
    this.marks.set(key(m.ref, m.p), m);
  }

  loadPack(pk: Pack): void {
    this.packs.set(pk.id, pk);
  }

  loadTotal(t: Total): void {
    this.totals.set(key(key(t.p, t.month), t.device), t);
    this.track(t.p, t.month, t.device, true);
  }

  loadIncrements(i: Increments): void {
    this.increments.set(key(i.p, i.month), i);
    this.track(i.p, i.month, '', false);
  }

  loadAlbum(a: AlbumRec): void {
    this.albums.set(a.id, a);
  }

  loadItem(i: AlbumItem): void {
    this.items.set(key(i.aid, i.id), i);
  }
}
