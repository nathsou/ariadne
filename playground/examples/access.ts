// Access control for a shared document. Each method becomes a function from the old state to the
// new one; the translator also proves, for every method, which fields it leaves alone.

export type Role = "viewer" | "editor" | "owner";

export class Access {
  private roles = new Map<string, Role>();
  private suspended = new Map<string, boolean>();

  /** Whether `user` may change who has access: an owner who is not suspended. */
  isOwner(user: string): boolean {
    if (this.suspended.has(user)) return false;
    const role = this.roles.get(user);
    if (role == null) return false;
    return role === "owner";
  }

  canRead(user: string): boolean {
    if (this.suspended.has(user)) return false;
    return this.roles.has(user);
  }

  canWrite(user: string): boolean {
    if (this.suspended.has(user)) return false;
    const role = this.roles.get(user);
    if (role == null) return false;
    return role === "editor" || role === "owner";
  }

  /** `by` gives `user` a role; only owners may. */
  grant(by: string, user: string, role: Role): void {
    if (!this.isOwner(by)) return;
    this.roles.set(user, role);
  }

  /** `by` takes away `user`'s role; only owners may, and not their own. */
  revoke(by: string, user: string): void {
    if (!this.isOwner(by) || by === user) return;
    this.roles.delete(user);
  }

  /** `by` suspends `user`, for good. */
  suspend(by: string, user: string): void {
    if (!this.isOwner(by) || by === user) return;
    this.suspended.set(user, true);
  }

  /** The first owner, of a new document. */
  claim(user: string): void {
    if (this.roles.size > 0) return;
    this.roles.set(user, "owner");
  }
}
