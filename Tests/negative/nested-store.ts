// expect: A1001
// An inner map is stored only new.
export class G {
  private m = new Map<string, Map<string, boolean>>();
  f(g: string): void {
    this.m.set("copy", this.m.get(g) ?? new Map<string, boolean>());
  }
}
