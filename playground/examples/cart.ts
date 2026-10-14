// This one is not in the subset (yet): Ariadne refuses it, and says why. In the model, arrays and
// records are values, so changing one in place (push, xs[i] = v, p.x = v) has no meaning there.
// The diagnostic suggests the fix; apply it and the program translates.

export type Item = { sku: string; price: number; quantity: number };

/** The cart with `item` added. */
export function addItem(cart: Item[], item: Item): Item[] {
  cart.push(item);
  return cart;
}

/** What the cart costs. */
export function total(cart: readonly Item[]): number {
  let sum = 0;
  for (const item of cart) {
    sum += item.price * item.quantity;
  }
  return sum;
}
