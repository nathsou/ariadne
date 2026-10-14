// expect: A2002
// `this` is never a value: an alias would let the maps be shared.
export class C {
  private m = new Map<string, number>();
  f(): number {
    const self = this;
    return 0;
  }
}
