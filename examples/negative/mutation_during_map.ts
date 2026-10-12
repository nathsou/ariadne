// expected: A3002
function f(): number[] { const a = [1, 2]; return a.map((x: number) => { a.push(x); return x; }); }
