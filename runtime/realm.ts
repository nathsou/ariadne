/**
 * Optional host bootstrap, outside the translated subset.
 * Call once in a NEW, PRISTINE realm before loading any application code.
 * This prevents later prototype pollution; it cannot repair earlier pollution.
 * Incoming references must still be ordinary, exclusively owned objects, not proxies.
 */
export function hardenPristineRealm(): void {
  const globals = { Array, Map, Number, BigInt, String, Boolean, Math, Object, Function };
  for (const [name, intrinsic] of Object.entries(globals)) {
    if ('prototype' in intrinsic) Object.freeze(intrinsic.prototype);
    Object.freeze(intrinsic);
    Object.defineProperty(globalThis, name, {
      value: intrinsic,
      writable: false,
      enumerable: false,
      configurable: false,
    });
  }
}
