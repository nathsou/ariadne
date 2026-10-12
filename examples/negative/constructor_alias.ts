// expected: A3001
class View {
  private readonly values: readonly number[] = [];
  constructor(values: readonly number[]) { }
}
function f(): void { const values = [1]; const view = new View(values); }
