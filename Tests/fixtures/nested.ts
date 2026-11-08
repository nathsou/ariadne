export class Groups {
  private members = new Map<string, Map<string, boolean>>();
  private owner = new Map<string, string>();

  add(group: string, id: string): void {
    if (!this.members.has(group)) this.members.set(group, new Map<string, boolean>());
    this.members.get(group)?.set(id, true);
    this.owner.set(id, group);
  }

  remove(group: string, id: string): void {
    this.members.get(group)?.delete(id);
    this.owner.delete(id);
  }

  has(group: string, id: string): boolean {
    return (this.members.get(group) ?? new Map<string, boolean>()).get(id) != null;
  }

  count(group: string): number {
    return (this.members.get(group) ?? new Map<string, boolean>()).size;
  }

  list(group: string): string[] {
    return [...(this.members.get(group) ?? new Map<string, boolean>()).keys()];
  }

  ownerName(id: string): string {
    const o = this.owner.get(id);
    return (o?.length ?? 1) === 0 ? 'empty' : o ?? 'none';
  }
}
