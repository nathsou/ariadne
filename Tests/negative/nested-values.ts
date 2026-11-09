// expect: A1001
// The values of a map of maps are its inner maps.
export class G {
  private m = new Map<string, Map<string, boolean>>();
  f(): number {
    return [...this.m.values()].length;
  }
}
