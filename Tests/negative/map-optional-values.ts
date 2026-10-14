// expect: A2002
export class C {
  private m = new Map<string, string | undefined>();
  f(k: string): string | undefined {
    return this.m.get(k);
  }
}
