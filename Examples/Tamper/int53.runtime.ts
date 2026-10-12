// Generated ownership entry wrappers. Requires the Ariadne pristine realm contract.
type Int53 = number;
// Keep Math correspondence, integer correspondence and computed-guard checks
// independent of the larger Int53 regression artifact.
export function floorDivide(a: Int53, b: Int53): Int53 { return Math.floor(a / b); }
export function add(a: Int53, b: Int53): Int53 { return a + b; }
