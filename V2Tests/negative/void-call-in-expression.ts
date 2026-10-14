// expect: A2002
export class C {
  private m = new Map<string, number>();
  clear(k: string): void {
    this.m.delete(k);
  }
  f(k: string): boolean {
    const r = this.clear(k);
    return true;
  }
}
