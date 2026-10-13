// Observations of JavaScript values, as `ariadne2 batch` prints them for the model.
export const units = s => Array.from({ length: s.length }, (_, i) => s.charCodeAt(i));

export function observe(v) {
  if (v === undefined) return ['undefined'];
  if (v === null) return ['null'];
  switch (typeof v) {
    case 'boolean': return ['bool', v];
    // Negative zero is unobservable in the subset (see V2/Model/Eval.lean).
    case 'number': return ['number', Object.is(v, -0) ? '0' : String(v)];
    case 'bigint': return ['bigint', v.toString()];
    case 'string': return ['string', units(v)];
    case 'function': return ['function'];
    case 'object':
      if (Array.isArray(v)) return ['array', v.map(observe)];
      return ['record', Object.entries(v).map(([k, x]) => [k, observe(x)])];
    default: throw new Error(`unexpected value ${typeof v}`);
  }
}
