// Generated ownership entry wrappers. Requires the Ariadne pristine realm contract.
export function appendGroup(groups: Map<string, bigint[]>, key: string, value: bigint): void {
  groups.get(key)!.push(value);
}
