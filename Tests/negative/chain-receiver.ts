// expect: A1001
// Optional chaining applies to locals.
export class G {
  private m = new Map<string, string>();
  f(k: string): number {
    return this.m.get(k)?.length ?? 0;
  }
}
