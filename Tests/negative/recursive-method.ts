// expect: A1001
export class C {
  private m = new Map<string, number>();
  a(k: string): void {
    this.b(k);
  }
  b(k: string): void {
    this.a(k);
  }
}
