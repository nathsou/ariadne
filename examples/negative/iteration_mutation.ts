// expected: A3002
function f(): void { const xs = [1]; for (const x of xs) { xs.push(x); } }
