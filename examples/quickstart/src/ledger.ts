// A ledger: entries credit or debit an account; balances never go negative.

export type Entry = { kind: "credit"; amount: number } | { kind: "debit"; amount: number };

/** The balance after the entries, refusing a debit larger than the balance. */
export function balance(entries: readonly Entry[]): number {
  let total = 0;
  for (const e of entries) {
    switch (e.kind) {
      case "credit":
        total += e.amount;
        break;
      case "debit":
        if (e.amount <= total) total -= e.amount;
        break;
    }
  }
  return total;
}

export class Accounts {
  private balances = new Map<string, number>();
  private frozen = new Map<string, boolean>();

  credit(id: string, amount: number): void {
    if (this.frozen.has(id) || amount <= 0) return;
    this.balances.set(id, (this.balances.get(id) ?? 0) + amount);
  }

  freeze(id: string): void {
    this.frozen.set(id, true);
  }

  balanceOf(id: string): number {
    return this.balances.get(id) ?? 0;
  }
}
