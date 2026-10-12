/**
 * Optional host bootstrap, outside the translated subset.
 * Call once in a NEW, PRISTINE realm before loading any application code.
 * This prevents later prototype pollution; it cannot repair earlier pollution.
 * Incoming references must still be ordinary, exclusively owned objects, not proxies.
 */
export function hardenPristineRealm(): void {
  // `for...of` uses iterator prototypes as well as collection prototypes.
  const iterators = [[][Symbol.iterator](), new Map().entries(), new Set().values()];
  for (const iterator of iterators) {
    let prototype = Object.getPrototypeOf(iterator);
    while (prototype !== null) {
      Object.freeze(prototype);
      prototype = Object.getPrototypeOf(prototype);
    }
  }
  const globals = { Array, Map, Set, Number, BigInt, String, Boolean, Math, Object, Function };
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
