type Int53 = number;

type Candidate =
  | { readonly kind: 'valid'; readonly version: Int53; readonly id: string }
  | { readonly kind: 'rejected'; readonly reason: string };

// Equal (version, id) pairs denote the same candidate value.
export function choose(candidates: readonly Candidate[], floor: Int53): Candidate | undefined {
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
