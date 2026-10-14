// A leaderboard. `toSorted` takes a comparator, and JavaScript's sort is only specified when the
// comparator is consistent (a total preorder). So the model makes that a safety condition, and
// the proofs discharge it once for `byScore` with the `cmp_laws` tactic.

export type Player = { name: string; score: number };

/** Higher scores first; equal scores by name. */
function byScore(a: Player, b: Player): number {
  if (a.score !== b.score) return a.score > b.score ? -1 : 1;
  if (a.name !== b.name) return a.name < b.name ? -1 : 1;
  return 0;
}

/** The players, best first. */
export function ranking(players: readonly Player[]): Player[] {
  return players.toSorted(byScore);
}

/** The best score, if there are players. */
export function best(players: readonly Player[]): number | undefined {
  const top = ranking(players)[0];
  return top == null ? undefined : top.score;
}

/** The names of the players whose score reaches `threshold`, best first. */
export function qualified(players: readonly Player[], threshold: number): string[] {
  return ranking(players)
    .filter((p) => p.score >= threshold)
    .map((p) => p.name);
}
