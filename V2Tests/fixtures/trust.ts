// drive's core/kernel/trust.ts (nathsou/drive 1e41c79), with one rewrite: the block-bodied
// callback in repairs() is lifted into repairOne() (v2 callbacks have expression bodies).
// The trust kernel: which stored copy of a key file (vault.uvf, meta/keys.uvf) a device may use, and which copies it
// may overwrite. Pure decisions over facts that decryption established: no I/O, no crypto, no clock. Providers are fully
// malicious storage; what they control reaches these functions only as an outcome of authenticated decryption (a copy
// opened, its seeds, written stamp and recovery status) or as the bare fact that a copy couldn't be opened or read.
//
// This file is in the verified kernel (docs/VERIFIED_KERNEL.md): it is written in the subset the translator accepts,
// translated to verify/Drive/Kernel/Trust.lean, and its properties are proven there for any number of copies
// (verify/Drive/Spec/Trust.lean). scripts/check-trust.ts still checks them over small worlds, with real crypto too.

/** How a copy a recovery key opened stands (see recoveryStatus): 'none' when no recovery key opened it. */
export type Recovery = 'none' | 'ok' | 'legacy' | 'bad';

/** The payload commitment of the factor that opened a copy (see commitmentStatus): 'none' when no factor opened it. */
export type Commit = 'ok' | 'legacy' | 'bad' | 'none';

/** What trying the factors (or a known CEK) on one stored copy established. */
export type CopyFact =
  /** No factor applies: a copy for other unlock methods, or for nobody. */
  | { kind: 'unopened' }
  /** A factor applies, but the copy doesn't authenticate: damaged, edited, or of an unknown format. */
  | { kind: 'damaged' }
  /**
   * Authenticated: its seeds (key generations), its written stamp, how a recovery key stands with it, and how its payload
   * commitment for the opening factor stands ('bad' too when it contradicts what the device knows, see Vault.open).
   */
  | { kind: 'opened'; written: number; seeds: string[]; recovery: Recovery; commit: Commit; kid?: string };

/** What a device remembers of the vault metadata it last used (see Vault.floor). */
export interface Floor {
  written: number;
  seed: string;
  /** Recovery keys whose copies carry tags: an untagged copy one of them opens was not written by the owner. */
  tagged?: string[];
  /** Factors whose copies carry commitments: a copy one of them opens without its commitment was not written by the owner. */
  committed?: string[];
}

export type Refusal = 'none' | 'wrong-key' | 'damaged' | 'not-owner' | 'older';

/**
 * A copy worth trying. `trusted` is false for a copy nothing vouches for beyond decryption (a recovery key opened it
 * without its tag, or its factor's commitment is missing where commitments are known); `committed`: the opening factor's
 * commitment matched.
 */
export interface Ranked {
  index: number;
  trusted: boolean;
  committed: boolean;
}

/** Copies worth trying, best first, or why none is. */
export type Choice = { ok: true; order: Ranked[] } | { ok: false; refused: Refusal };

/** An acceptable copy with what ranks it. */
interface Candidate {
  index: number;
  committed: boolean;
  tagged: boolean;
  seeds: number;
  written: number;
}

/** Whether the factor `kid` is on a list the device keeps (an empty kid is on none). */
function listed(kid: string | undefined, list: string[] | undefined): boolean {
  if (kid == null) return false;
  if (list == null) return false;
  return kid !== '' && list.includes(kid);
}

/** Committed first, then tagged, then the newest generation (most seeds), then the newest stamp, then the first. */
function byRank(a: Candidate, b: Candidate): number {
  if (a.committed !== b.committed) return a.committed ? -1 : 1;
  if (a.tagged !== b.tagged) return a.tagged ? -1 : 1;
  if (a.seeds !== b.seeds) return a.seeds > b.seeds ? -1 : 1;
  if (a.written !== b.written) return a.written > b.written ? -1 : 1;
  if (a.index !== b.index) return a.index < b.index ? -1 : 1;
  return 0;
}

/**
 * Which copies of vault.uvf to use, best first. Never one whose commitment or recovery tag is wrong, nor one without the
 * commitment (or tag) of its factor when the device knows that factor commits (or tags), nor one missing the latest seed
 * the device used (an older generation: rolled back, or written by a device a rotation removed). Of the rest: committed
 * first (a device the rotation removed can't commit for another factor), then tagged (or not opened by a recovery key),
 * then the newest generation (most seeds), then the newest written stamp.
 */
export function chooseVaultCopy(facts: CopyFact[], floor?: Floor | null): Choice {
  const committedFactors = floor == null ? undefined : floor.committed;
  const taggedFactors = floor == null ? undefined : floor.tagged;
  const floorSeed = floor == null ? '' : floor.seed;
  let ok: Candidate[] = [];
  let opened = false;
  let damaged = false;
  let notOwner = false;
  let older = false;
  for (const [index, f] of facts.entries()) {
    switch (f.kind) {
      case 'unopened':
        continue;
      case 'damaged':
        damaged = true;
        continue;
      case 'opened': {
        opened = true;
        if (f.commit === 'bad' || f.recovery === 'bad') {
          notOwner = true;
          continue;
        }
        if ((f.commit === 'legacy' && listed(f.kid, committedFactors)) || (f.recovery === 'legacy' && listed(f.kid, taggedFactors))) {
          notOwner = true;
          continue;
        }
        if (floorSeed !== '' && !f.seeds.includes(floorSeed)) {
          older = true;
          continue;
        }
        ok = [...ok, { index, committed: f.commit === 'ok', tagged: f.recovery !== 'legacy', seeds: f.seeds.length, written: f.written }];
      }
    }
  }
  if (ok.length > 0) {
    const ranked = ok.toSorted(byRank);
    // Untrusted: a recovery key's copy without its tag, or (once any copy shows commitments) one without its commitment.
    const anyCommitted = ranked.some((x) => x.committed);
    return { ok: true, order: ranked.map((x) => ({ index: x.index, trusted: x.tagged && (x.committed || !anyCommitted), committed: x.committed })) };
  }
  return { ok: false, refused: older ? 'older' : notOwner ? 'not-owner' : damaged ? 'damaged' : opened || facts.length > 0 ? 'wrong-key' : 'none' };
}

/** The copy of meta/keys.uvf a device uses. */
export interface KeysChoice {
  index: number;
  trusted: boolean;
}

/** The best keys copy so far, with its stamp. */
interface BestKeys {
  index: number;
  trusted: boolean;
  written: number;
}

/** The copy of meta/keys.uvf to use: never one with a wrong recovery tag; tagged ones first, then the newest. */
export function chooseKeysCopy(facts: CopyFact[]): KeysChoice | null {
  let best: BestKeys | null = null;
  for (const [index, f] of facts.entries()) {
    switch (f.kind) {
      case 'unopened':
      case 'damaged':
        continue;
      case 'opened': {
        if (f.recovery === 'bad') continue;
        const trusted = f.recovery !== 'legacy';
        const better = best == null ? true : (trusted && !best.trusted) || (trusted === best.trusted && f.written > best.written);
        if (better) best = { index, trusted, written: f.written };
      }
    }
  }
  return best == null ? null : { index: best.index, trusted: best.trusted };
}

/**
 * The base for changing a key file this session holds: the newest copy of its own generation (the session's CEK opens
 * it, which authenticates its stamp), `-1` when the session's own is the newest. `stamps` are null for copies the CEK
 * doesn't open: they never become the base.
 */
export function newestOwnCopy(own: number, stamps: (number | null)[]): number {
  let best = -1;
  let newest = own;
  for (const [i, stamp] of stamps.entries()) {
    if (stamp == null) continue;
    if (stamp > newest) {
      best = i;
      newest = stamp;
    }
  }
  return best;
}

/**
 * Whether the unlock methods may be changed from a copy written at `written`: never from one older than what this
 * device saw before (`floorWritten`), which could bring back what was removed since.
 */
export function mayChangeFrom(written: number, floorWritten: number): boolean {
  return written >= floorWritten;
}

/** One provider's copy as a repair sees it. */
export type StoredCopy =
  /** The provider says there is none. */
  | { state: 'missing' }
  /** The provider couldn't say (unreachable, an error). */
  | { state: 'unknown' }
  /** This session's generation (its CEK opens it), written at `written`. */
  | { state: 'own'; written: number }
  /** Known to be older than this session's: an earlier generation the factors opened, or one opening with a retired CEK. */
  | { state: 'older' }
  /** A factor applied but it didn't authenticate, or it isn't a JWE at all. */
  | { state: 'damaged' }
  /** Nothing this session knows opens it: maybe a newer generation (a rotation elsewhere), maybe planted. */
  | { state: 'foreign' };

/** What a repair may do: nothing when the session is stale (another device rotated past it) or read-only. */
export interface RepairContext {
  stale: boolean;
  readOnly: boolean;
}

/** Whether the provider answered for its copy. */
function answered(c: StoredCopy): boolean {
  switch (c.state) {
    case 'unknown':
      return false;
    default:
      return true;
  }
}

/**
 * Which providers' copies of a key file a session may overwrite with its own (written at `own`). Nothing when the session
 * is read-only or knows another device rotated past it (stale). A missing copy only when every provider answered (an
 * unreachable one may hold a newer copy), an own-generation copy only when older, an older or damaged one always. A
 * foreign copy never: it may be a rotation whose marker didn't reach the providers, and overwriting it would undo it.
 */
/** Whether a repair may overwrite one copy, given whether every provider answered. */
function repairOne(c: StoredCopy, own: number, allAnswered: boolean): boolean {
  switch (c.state) {
    case 'missing':
      return allAnswered;
    case 'own':
      return c.written < own;
    case 'older':
    case 'damaged':
      return true;
    case 'unknown':
    case 'foreign':
      return false;
  }
}

export function repairs(copies: StoredCopy[], own: number, ctx: RepairContext): boolean[] {
  if (ctx.stale || ctx.readOnly) return copies.map(() => false);
  const allAnswered = copies.every(answered);
  return copies.map((c) => repairOne(c, own, allAnswered));
}

/**
 * Whether a copy the confirmed factors of a rotation open shows another device rotated past this session: it holds a
 * seed this session doesn't know. A rotation then refuses (it would remove what that device added).
 */
export function rotatedPast(copySeeds: string[], ownSeeds: string[]): boolean {
  return copySeeds.some((id) => !ownSeeds.includes(id));
}
