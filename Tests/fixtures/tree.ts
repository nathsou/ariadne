// drive core/kernel/tree.ts (nathsou/drive 1e41c79), unchanged.
// The index's file tree: where each node wants to be, where it sits, and what is buried. Every node has a position
// register (the parent and name of its latest move, else of its earliest creation); where nodes sit is derived from
// those registers alone (a move that would close a cycle waits at the root, the newest one on the cycle), and so is
// burial (a node is buried while it or a node above it is purged). IndexState (core/index/state.ts) keeps the nodes'
// contents and hands the tree its positions and purges.
//
// Part of the verified kernel (docs/VERIFIED_KERNEL.md): written in its subset, translated to Lean
// (verify/Drive/Kernel/Tree.lean), printed back and run against it. A parent's children are a linked list (each node
// knows its neighbours), so adding or removing one doesn't copy the others, and walks are counted loops bounded by the
// number of nodes. Node ids are never empty: `''` stands for no node.

/** Where a node wants to be: the parent and name of its latest move, else of its earliest creation. */
export interface Spot {
  want: string;
  name: string;
  /** Stamp of the latest move. */
  pos?: string;
  /** Stamp of the earliest creation. */
  made?: string;
}

/** Where a node sits: its parent, and its neighbours among the parent's children (in the order they came). */
interface Link {
  parent: string;
  prev?: string;
  next?: string;
}

/** A parent's first and last children. */
interface Ends {
  first: string;
  last: string;
}

function root(): string {
  return 'root';
}

/** Whether a write at `stamp` replaces one at `s` (absent or empty: never written). */
function newer(s: string | undefined, stamp: string): boolean {
  if (s == null) return true;
  return s === '' || s < stamp;
}

/** Whether a first-writer-wins register written at `s` takes a write at `stamp`. */
function earlier(s: string | undefined, stamp: string): boolean {
  if (s == null) return true;
  return s === '' || stamp < s;
}

/** The earlier of two stamps (`''`: none). */
function minStamp(a: string, b: string): string {
  if (a === '') return b;
  if (b === '') return a;
  return a < b ? a : b;
}

function orNone(s: string | undefined): string {
  return s == null ? '' : s;
}

/** The order of moves on a cycle: by the stamp that placed each node, then by id. */
function key(s: Spot, id: string): string {
  const pos = s.pos;
  const stamp = pos == null ? orNone(s.made) : pos;
  return stamp + '\n' + id;
}

export class Tree {
  /** Where each node wants to be: the nodes that exist (the root isn't one). */
  private spots = new Map<string, Spot>();
  /** Where each node sits. */
  private links = new Map<string, Link>();
  /** The first and last children of each parent that has some. */
  private ends = new Map<string, Ends>();
  /** Nodes kept at the root because the move they want would close a cycle. */
  private detached = new Map<string, boolean>();
  /** Parents that nodes sit under but that don't exist (yet): those nodes show at the root. */
  private waiting = new Map<string, boolean>();
  /** The earliest purge of each node (or of an id that doesn't exist). */
  private purged = new Map<string, string>();
  /** What buries each buried node: the earliest purge of it or of a node above it. */
  private buried = new Map<string, string>();
  /** Nodes whose spot, parent or burial changed since `clearChanges()`. */
  private changed = new Map<string, boolean>();

  // ---- positions ----

  /** The first operation creating a node: it wants to be at `parent` under `name`. */
  create(id: string, parent: string, name: string, stamp: string): void {
    if (id === root() || this.spots.has(id)) return;
    this.spots.set(id, { want: parent, name, made: stamp });
    this.waiting.delete(id);
    this.changed.set(id, true);
    this.rearrange(id);
  }

  /**
   * Another place for a node: a move (`move`: the latest wins) or another operation creating it (the earliest wins,
   * until the node is moved: puts of later versions carry a position too, which must not count as moves).
   */
  position(id: string, parent: string, name: string, stamp: string, move: boolean): void {
    const s = this.spots.get(id);
    if (s == null) return;
    if (move) {
      if (!newer(s.pos, stamp)) return;
      this.spots.set(id, { ...s, want: parent, name, pos: stamp });
    } else {
      if (!earlier(s.made, stamp)) return;
      if (orNone(s.pos) !== '') {
        this.spots.set(id, { ...s, made: stamp });
        this.changed.set(id, true);
        return;
      }
      this.spots.set(id, { ...s, want: parent, name, made: stamp });
    }
    this.changed.set(id, true);
    this.rearrange(id);
  }

  /** Re-derives where nodes sit once `id` wants another parent: only cycles through it can form, and nodes detached
   * from a cycle it broke get their parent back. */
  private rearrange(id: string): void {
    const cycle = this.cycleOf(id);
    const detached = [...this.detached.keys()];
    this.attach(id);
    for (const x of cycle) this.attach(x);
    for (const x of detached) this.attach(x);
  }

  /** The nodes on the cycle of wanted parents through `id`, from `id` on (none if it isn't on one). */
  private cycleOf(id: string): string[] {
    // A walk up visits each node at most once before it repeats: no more steps than there are nodes.
    const steps = this.spots.size;
    let cur = id;
    let on = false;
    for (let _step = 0; _step < steps; _step++) {
      const s = this.spots.get(cur);
      if (s == null) return [];
      cur = s.want;
      if (cur === id) {
        on = true;
        break;
      }
    }
    if (!on) return [];
    let path: string[] = [id];
    cur = id;
    for (let _step = 0; _step < steps; _step++) {
      const s = this.spots.get(cur);
      if (s == null) return path;
      if (s.want === id) return path;
      cur = s.want;
      path = [...path, cur];
    }
    return path;
  }

  private keyOf(id: string): string {
    const s = this.spots.get(id);
    if (s == null) return '';
    return key(s, id);
  }

  /**
   * Puts a node under the parent it wants, unless that closes a cycle in which its move is the newest: then it waits
   * at the root. Depends only on the spots, so concurrent moves end the same everywhere. A node that moved has its
   * burial re-derived, with what is under it.
   */
  private attach(id: string): void {
    const s = this.spots.get(id);
    if (s == null) return;
    const cycle = this.cycleOf(id);
    const mine = key(s, id);
    const detach = cycle.length > 0 && cycle.every((c) => c === id || this.keyOf(c) < mine);
    if (detach) this.detached.set(id, true);
    else this.detached.delete(id);
    const parent = detach ? root() : s.want;
    if (this.parentOf(id) === parent) return;
    this.unlink(id);
    this.link(id, parent);
    this.changed.set(id, true);
    this.settle(id, false);
  }

  // ---- children: a linked list per parent ----

  /** Puts a node last among `parent`'s children. */
  private link(id: string, parent: string): void {
    const last = this.lastChild(parent);
    if (last === '') {
      this.ends.set(parent, { first: id, last: id });
      this.links.set(id, { parent });
    } else {
      this.setNext(last, id);
      this.links.set(id, { parent, prev: last });
      this.ends.set(parent, { first: this.firstChild(parent), last: id });
    }
    if (parent !== root() && !this.spots.has(parent) && !this.purged.has(parent)) this.waiting.set(parent, true);
  }

  /** Takes a node out of its parent's children. */
  private unlink(id: string): void {
    const l = this.links.get(id);
    if (l == null) return;
    this.links.delete(id);
    const e = this.ends.get(l.parent);
    if (e == null) return;
    const prev = orNone(l.prev);
    const next = orNone(l.next);
    if (prev === '' && next === '') {
      this.ends.delete(l.parent);
      this.waiting.delete(l.parent);
      return;
    }
    if (prev !== '') this.setNext(prev, l.next);
    if (next !== '') this.setPrev(next, l.prev);
    this.ends.set(l.parent, { first: prev === '' ? next : e.first, last: next === '' ? prev : e.last });
  }

  private setNext(id: string, next: string | undefined): void {
    const l = this.links.get(id);
    if (l == null) return;
    this.links.set(id, { ...l, next });
  }

  private setPrev(id: string, prev: string | undefined): void {
    const l = this.links.get(id);
    if (l == null) return;
    this.links.set(id, { ...l, prev });
  }

  // ---- burial ----

  /** A purge of a node, or of an id that doesn't exist (yet): the earliest wins. */
  purge(id: string, stamp: string): void {
    if (id === root()) return;
    if (!earlier(this.purged.get(id), stamp)) return;
    this.purged.set(id, stamp);
    this.waiting.delete(id);
    this.settle(id, false);
  }

  /** What buries a node: the earliest purge of it or of a node above it (`''`: nothing). */
  private burialOf(id: string): string {
    const p = this.parentOf(id);
    const above = p === '' || p === root() ? '' : orNone(this.spots.has(p) ? this.buried.get(p) : this.purged.get(p));
    return minStamp(orNone(this.purged.get(id)), above);
  }

  private bury(id: string, by: string): void {
    this.changed.set(id, true);
    if (by === '') this.buried.delete(id);
    else this.buried.set(id, by);
  }

  /**
   * Re-derives burial from `start` down: a node is buried while it or a node above it is purged, by the earliest of
   * those purges. Descendants are only visited when something changed (or for every node with `all`).
   */
  private settle(start: string, all: boolean): void {
    // A walk down the children and back up: each node is entered once and left once.
    const steps = 2 * this.links.size + 2;
    let cur = start;
    let down = true;
    for (let _step = 0; _step < steps; _step++) {
      if (down) {
        let deeper = true;
        if (cur !== root() && this.spots.has(cur)) {
          const by = this.burialOf(cur);
          if (by !== orNone(this.buried.get(cur))) this.bury(cur, by);
          else deeper = all;
        }
        const first = deeper ? this.firstChild(cur) : '';
        if (first !== '') {
          cur = first;
          continue;
        }
        down = false;
      }
      // Leaving `cur`: to its next sibling, else up to its parent, until back at `start`.
      if (cur === start) return;
      const next = this.nextSibling(cur);
      if (next !== '') {
        cur = next;
        down = true;
        continue;
      }
      cur = this.parentOf(cur);
    }
  }

  // ---- snapshots ----

  /** A node from a snapshot, before any is linked: where it wants to be. */
  loadSpot(id: string, s: Spot): void {
    if (id === root()) return;
    this.spots.set(id, s);
    this.changed.set(id, true);
  }

  loadPurge(id: string, stamp: string): void {
    this.purged.set(id, stamp);
  }

  /** Where a node from a snapshot sat, once every node is loaded. */
  loadLink(id: string, parent: string): void {
    if (!this.spots.has(id) || this.links.has(id)) return;
    this.link(id, parent);
  }

  /** Re-attaches the loaded nodes that sit elsewhere than they want to be or are on a cycle, then re-derives burial. */
  untangle(): void {
    for (const id of [...this.spots.keys()]) {
      const s = this.spots.get(id);
      if (s == null) continue;
      if (this.parentOf(id) !== s.want || this.cycleOf(id).length > 0) this.attach(id);
    }
    this.settle(root(), true);
    for (const p of [...this.ends.keys()]) if (p !== root() && !this.spots.has(p)) this.settle(p, true);
  }

  // ---- queries ----

  spotOf(id: string): Spot | undefined {
    return this.spots.get(id);
  }

  /** The parent a node sits under, or `''`. */
  parentOf(id: string): string {
    const l = this.links.get(id);
    return l == null ? '' : l.parent;
  }

  firstChild(id: string): string {
    const e = this.ends.get(id);
    return e == null ? '' : e.first;
  }

  private lastChild(id: string): string {
    const e = this.ends.get(id);
    return e == null ? '' : e.last;
  }

  nextSibling(id: string): string {
    const l = this.links.get(id);
    return l == null ? '' : orNone(l.next);
  }

  isDetached(id: string): boolean {
    return this.detached.has(id);
  }

  /** What buries a node, if it is buried. */
  burial(id: string): string | undefined {
    return this.buried.get(id);
  }

  isPurged(id: string): boolean {
    return this.purged.has(id);
  }

  purgeOf(id: string): string | undefined {
    return this.purged.get(id);
  }

  purgedIds(): string[] {
    return [...this.purged.keys()];
  }

  waitingIds(): string[] {
    return [...this.waiting.keys()];
  }

  hasWaiting(): boolean {
    return this.waiting.size > 0;
  }

  changes(): string[] {
    return [...this.changed.keys()];
  }

  clearChanges(): void {
    for (const id of [...this.changed.keys()]) this.changed.delete(id);
  }
}
