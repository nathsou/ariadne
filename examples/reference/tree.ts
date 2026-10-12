type Int53 = number;

export class Tree {
  private readonly parents = new Map<string, string>();
  private readonly children = new Map<string, string[]>();

  add(node: string): void {
    if (!this.children.has(node)) { this.children.set(node, []); }
  }

  parent(node: string): string | undefined { return this.parents.get(node); }

  childList(node: string): string[] { return (this.children.get(node) ?? []).slice(); }

  move(node: string, parent: string | undefined): void {
    this.add(node);
    if (parent !== undefined) { this.add(parent); }
    const old = this.parents.get(node);
    if (old !== undefined) {
      const siblings = this.children.get(old) ?? [];
      this.children.set(old, siblings.filter((child: string) => child !== node));
    }
    this.parents.delete(node);
    let cursor = parent;
    for (let i = 0; i < this.children.size; i++) {
      if (cursor === node) { return; }
      if (cursor === undefined) { break; }
      cursor = this.parents.get(cursor);
    }
    if (parent !== undefined) {
      this.parents.set(node, parent);
      const siblings = this.children.get(parent) ?? [];
      this.children.set(parent, [...siblings, node]);
    }
  }

  root(node: string): string {
    let cursor = node;
    for (let i = 0; i < this.children.size; i++) {
      const parent = this.parents.get(cursor);
      if (parent === undefined) { return cursor; }
      cursor = parent;
    }
    return cursor;
  }
}
