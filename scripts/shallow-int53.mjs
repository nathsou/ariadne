import { resolve } from 'node:path';
import { writeFile, mkdir, mkdtemp, rm } from 'node:fs/promises';
import { spawnSync } from 'node:child_process';
import assert from 'node:assert/strict';
import * as js from '../examples/shallow/int53.ts';
const max = 9007199254740991;
const cases = {
  less: [[[1,2],true], [[max,-max],true]],
  equal: [[[max,max],true], [[0,1],true]],
  atMost: [[[-max,-max],true], [[max,0],true]],
  incrementTwice: [[[0],true], [[max-2],true], [[max-1],false]],
  localAbsolute: [[[0],true], [[-max],true]],
  add: [[[1,2],true], [[max,0],true], [[max,1],false], [[-max,max],true]],
  multiply: [[[3,4],true], [[-1,0],false], [[0,-1],false], [[0,1],true], [[max,2],false]],
  negate: [[[0],false], [[1],true], [[-max],true]],
  remainder: [[[-7,3],true], [[-6,3],false], [[7,0],false], [[7,-3],true]],
  floorDivide: [[[-7,3],true], [[7,-3],true], [[0,-3],false], [[1,0],false]],
  truncDivide: [[[-7,3],true], [[-1,3],false], [[7,-3],true], [[1,0],false]],
  absolute: [[[-max],true], [[0],true]], minimum: [[[3,-2,1],true]], maximum: [[[-3,2],true]],
  widen: [[[max],true], [[-2],true]], count: [[[[]],true], [[[1,max]],true]],
  chooseBranch: [[[max,false],true], [[max,true],false], [[max+1,false],false]],
  total: [[[[]],true], [[[1,2,3]],true], [[[max,1,-1]],false]],
  firstZero: [[[[0,max]],true], [[[max,0]],false], [[[1,0,max]],true], [[[1,2]],true]],
  through: [[[8,3],true], [[8,-1],true], [[0,-1],true]],
  optionalEqual: [[[undefined,2],true], [[2,2],true], [[2,3],true]],
  optionalPair: [[[undefined,undefined],true], [[2,undefined],true], [[undefined,2],true], [[2,2],true]],
};
const bits = value => {
  const view = new DataView(new ArrayBuffer(8));
  // The model canonicalizes NaN; engines may choose different NaN signs/payloads.
  view.setFloat64(0, Number.isNaN(value) ? NaN : value);
  return view.getBigUint64(0).toString();
};
const observe = value => typeof value === 'boolean' ? ['boolean', value] : ['number', bits(value)];
const argument = (value, optional=false) => optional ? value === undefined ? '(none : Option Int)' : `(some (${value} : Int))` :
  Array.isArray(value) ? `([${value}] : List Int)` : typeof value === 'boolean' ? String(value) : `(${value} : Int)`;
await mkdir('work', {recursive: true});
const dir = await mkdtemp(resolve('work/shallow-int53-'));
try {
  let runner = 'import Examples.Shallow.int53\nimport Ariadne.Observe\nopen Ariadne\nopen Extracted_int53.Shallow\n';
  const expected=[];
  let count=0;
  for (const [name, entries] of Object.entries(cases)) for (const [args, safe] of entries) {
    const nativeArgs = args.map((value,i) => argument(value, name==='optionalPair' || name==='optionalEqual' && i===0)).join(' ');
    runner += `#eval IO.println (Lean.toJson (decide (${name}.safe ${nativeArgs}))).compress\n`;
    expected.push(safe);
    const result = js[name](...args);
    const heap=[];
    const value = x => {
      if (Array.isArray(x)) {const index=heap.length; heap.push(`.array [${x.map(value)}]`);return `.ref ${index}`;}
      if (x===undefined) return 'Value.undefined';
      if (typeof x==='boolean') return `.boolean ${x}`;
      return `.number (Float.Model.ofInt (${x}))`;
    };
    const values=args.map(value);
    runner += `#eval IO.println ((observeResult (Ariadne.apply Extracted_int53.program 10000 {heap := [${heap}]} (.function "${name}") [${values}])).compress)\n`;
    expected.push({ok:observe(result)});
    if (safe) {
      const called=`(${name} ${nativeArgs})`;
      const encoded=typeof result==='boolean' ? `.boolean ${called}` : name==='widen' ? `.number ${called}` : `.number (Float.Model.ofInt ${called})`;
      runner += `#eval IO.println ((observeResult (.ok (${encoded}, {}))).compress)\n`;
      expected.push({ok:observe(result)});
    }
    count++;
  }
  await writeFile(`${dir}/Compare.lean`,runner);
  const output=spawnSync('lake',['env','lean',`${dir}/Compare.lean`],{encoding:'utf8',timeout:180000,maxBuffer:8e6});
  assert.equal(output.status,0,output.stdout+output.stderr);
  assert.deepEqual(output.stdout.trim().split('\n').map(JSON.parse),expected);
  console.log(`Int53 passed: ${count} safety checks, operational comparisons, and native comparisons under true guards.`);
} finally {await rm(dir,{recursive:true,force:true});}
