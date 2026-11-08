// expect: A1001
// An inner map read as a value could be changed through its entry later.
export class G {
  private m = new Map<string, Map<string, boolean>>();
  f(g: string): number {
    const x = this.m.get(g);
    return x == null ? 0 : 1;
  }
}
