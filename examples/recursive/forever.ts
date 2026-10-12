// Used to prove exhaustion at every budget, not just at a selected timeout.
export function forever(): bigint {
  return forever();
}
