// Lossless scalar encodings shared by the compiler differential tests.
function bits(value) {
  const bytes = new DataView(new ArrayBuffer(8));
  bytes.setFloat64(0, Number.isNaN(value) ? NaN : value);
  return bytes.getBigUint64(0).toString();
}
const units = value => Array.from({ length: value.length }, (_, i) => value.charCodeAt(i));
export function observe(value) {
  if (value === undefined) return ['undefined'];
  if (typeof value === 'bigint') return ['bigint', value.toString()];
  if (typeof value === 'number') return ['number', bits(value)];
  if (typeof value === 'string') return ['string', units(value)];
  if (typeof value === 'boolean') return ['boolean', value];
  throw new Error('Unsupported test value');
}
export function lean(value) {
  if (value === undefined) return '.undefined';
  if (typeof value === 'bigint') return `(.bigint (${value}))`;
  if (typeof value === 'number') return `(.number (Float.Model.ofBits ${bits(value)}))`;
  if (typeof value === 'string') return `(.string [${units(value).join(', ')}])`;
  if (typeof value === 'boolean') return `(.boolean ${value})`;
  throw new Error('Unsupported test value');
}
