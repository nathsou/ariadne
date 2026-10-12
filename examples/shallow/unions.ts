type Candidate =
  | { readonly kind: 'valid'; readonly version: bigint; readonly id: string }
  | { readonly kind: 'rejected'; readonly reason: string };

export function valid(version: bigint, id: string): Candidate {
  return { kind: 'valid', version: version, id: id };
}
export function rejected(reason: string): Candidate { return { kind: 'rejected', reason: reason }; }
export function kind(candidate: Candidate): string { return candidate.kind; }
export function getVersion(candidate: Candidate): bigint | undefined {
  if (candidate.kind !== 'valid') { return undefined; }
  return candidate.version;
}
export function choose(candidates: readonly Candidate[], floor: bigint): Candidate | undefined {
  let best: Candidate | undefined = undefined;
  for (const candidate of candidates) {
    switch (candidate.kind) {
      case 'valid':
        if (candidate.version >= floor) {
          if (best === undefined || best.kind !== 'valid' ||
              candidate.version > best.version ||
              (candidate.version === best.version && candidate.id > best.id)) {
            best = candidate;
          }
        }
        break;
      case 'rejected':
        break;
    }
  }
  return best;
}

export function copyIfValid(candidate: Candidate): Candidate | undefined {
  if (candidate.kind === 'valid') { return candidate; }
  return undefined;
}

export function fallback(candidate: Candidate | undefined): Candidate {
  if (candidate === undefined) { return { kind: 'rejected', reason: 'missing' }; }
  return candidate;
}

export function replace(candidate: Candidate): Candidate {
  let result: Candidate = candidate;
  if (result.kind === 'valid') { result = rejected('replaced'); }
  return result;
}

export function filtered(candidates: readonly Candidate[], floor: bigint): Candidate[] {
  return candidates.filter((candidate: Candidate) => candidate.kind === 'valid' && candidate.version >= floor);
}

type Event =
  | { readonly kind: 'created'; readonly id: string }
  | { readonly kind: 'changed'; readonly value: bigint }
  | { readonly kind: 'deleted'; readonly id: string };

export function eventValue(event: Event): bigint {
  switch (event.kind) {
    case 'created': return 0n;
    case 'changed': return event.value;
    default: return -1n;
  }
}

export function eventTag(event: Event): string { return event.kind; }

export function changed(value: bigint): Event { return { kind: 'changed', value: value }; }
