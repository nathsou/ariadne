// expect: A2002
export class C {
  private m = new Map<string, number>();
  take(k: string): number {
    this.m.delete(k);
    return 0;
  }
}
