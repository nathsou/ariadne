// Native extraction of the original references, compared with both JavaScript
// and the operational evaluator. These finite traces do not replace M3/M4.
import { mkdir, mkdtemp, writeFile, rm } from 'node:fs/promises';
import { spawnSync } from 'node:child_process';
import { resolve } from 'node:path';
import assert from 'node:assert/strict';
import { choose } from '../examples/reference/decision.ts';
import { Registers } from '../examples/reference/registers.ts';
import { Tree } from '../examples/reference/tree.ts';

const units = s => Array.from({length:s.length}, (_,i) => s.charCodeAt(i));
const bits = n => {const view=new DataView(new ArrayBuffer(8));view.setFloat64(0,n);return view.getBigUint64(0).toString();};
const observe = value => value===undefined ? ['undefined'] : typeof value==='string' ? ['string',units(value)] :
  typeof value==='number' ? ['number',bits(value)] : Array.isArray(value) ? ['array',value.map(observe)] :
  ['record',Object.entries(value).map(([k,v])=>[k,observe(v)])];
const argument = value => value===undefined ? '(none : Option JSString)' : typeof value==='string' ? `([${units(value)}] : JSString)` : `(${value} : Int)`;
const scalar = value => value===undefined ? 'Value.undefined' : typeof value==='string' ? `(.string ${argument(value)})` : `(.number (Float.Model.ofInt ${argument(value)}))`;
function permutations(xs) {return xs.length ? xs.flatMap((x,i)=>permutations(xs.filter((_,j)=>i!==j)).map(rest=>[x,...rest])) : [[]];}
const candidates = [{kind:'valid',version:1,id:'a'}, {kind:'valid',version:2,id:'b'},
  {kind:'valid',version:2,id:'\ud800'}, {kind:'rejected',reason:'offline'}];
const decisionCases = [ [[],0], [[{kind:'valid',version:9007199254740991,id:'max'}],9007199254740991],
  ...[-1,1,2,3].flatMap(floor=>permutations(candidates).map(xs=>[xs,floor])) ];
const writes = [['write','a','b',1,'1'], ['write','a','b',4,'3'], ['write','a','b',2,'2']];
const registerTraces = [...permutations(writes), [...writes,...writes], [],
  ...permutations([1,3,2]).map(xs=>xs.map(value=>['count','k','r',value])),
  [['count','k','r',-1],['count','k','r',0],['count','k','r',2]],
  [['write','a','b',9007199254740991,'\ud800'],['write','a','c',9,'1']]];
const treeTraces = [[], [['move','a','b']], [['move','a','b'],['move','b','c']],
  [['move','a','b'],['move','b','c'],['move','c','a']],
  [['move','a','b'],['move','a','c'],['move','b','a']],
  [['move','a','a']], [['move','a','b'],['move','a',undefined]],
  [['add','a'],['add','a'],['move','a','b'],['move','a','b']],
  [['move','\ud800','a'],['move','a','\ud800']]];
const nodes=['a','b','c','\ud800'];
await mkdir('work',{recursive:true});
const dir=await mkdtemp(resolve('work/reference-shallow-'));
try {
  let runner=`import Examples.ShallowReference.decision
import Examples.ShallowReference.registers
import Examples.ShallowReference.tree
import Ariadne.Observe
open Ariadne
set_option linter.unusedVariables false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Decision
open Extracted_reference_decision.Shallow
def fields : NativeTypes.Candidate → List (String × Value)
  | .valid p => [("kind", .string [118,97,108,105,100]), ("version", .number (Float.Model.ofInt p.version)), ("id", .string p.id)]
  | .rejected p => [("kind", .string [114,101,106,101,99,116,101,100]), ("reason", .string p.reason)]
def value (candidate : NativeTypes.Candidate) : Value × State := (.ref 0, {heap := [.record (fields candidate)]})
`;
  const expected=[];
  for (const [i,[xs,floor]] of decisionCases.entries()) {
    const before=structuredClone(xs);
    const result=choose(xs,floor);
    assert.deepEqual(xs,before);
    const input=xs.map(x=>x.kind==='valid' ? `(NativeTypes.Candidate.valid ⟨${x.version}, ${argument(x.id)}⟩)` : `(NativeTypes.Candidate.rejected ⟨${argument(x.reason)}⟩)`);
    runner += `#eval IO.println (Lean.toJson (decide (choose.safe [${input}] (${floor})))).compress\n`;
    expected.push(true);
    runner += `#eval IO.println ((observeResult (.ok (((choose [${input}] (${floor})).map value).getD (.undefined, {})))).compress)\n`;
    expected.push({ok:observe(result)});
    const heap=[];
    const encode=value=>{
      if (typeof value!=='object') return scalar(value);
      const index=heap.length;heap.push(null);
      heap[index]=Array.isArray(value) ? `.array [${value.map(encode)}]` : `.record [${Object.entries(value).map(([k,v])=>`(${JSON.stringify(k)}, ${encode(v)})`)}]`;
      return `.ref ${index}`;
    };
    const encoded=encode(xs);
    runner += `def model${i} := Ariadne.apply Extracted_reference_decision.program 10000 {heap := [${heap}]} (.function "choose") [${encoded}, ${scalar(floor)}]\n`;
    runner += `#eval IO.println ((observeResult model${i}).compress)\n`;
    expected.push({ok:observe(result)});
    runner += `#eval IO.println ((observeResult (model${i}.map (fun (_,state)=>(${encoded},state)))).compress)\n`;
    expected.push({ok:observe(xs)});
  }
  runner+='end Decision\n';
  let traceCount=0;
  for (const [name,Class,traces,stem] of [['Registers',Registers,registerTraces,'registers'],['Tree',Tree,treeTraces,'tree']]) {
    const ns=`Extracted_reference_${stem}`;
    runner+=`namespace ${name}Traces\nopen ${ns}.Shallow\n`;
    for (const [i,ops] of traces.entries()) {
      const state=new Class();
      const results=[];
      let native=`def native${i} : List Lean.Json := Id.run do\n  let state0 := «${name}##new»\n`;
      let model=`def model${i} : Result (List Lean.Json) := do\n  let (receiver,state) ← evalExpr ${ns}.program 10000 {} (.newClass "${name}" [] {})\n  let .ref location := receiver | throw (.typeError "expected receiver")\n`;
      const nativeResults=[],modelResults=[];
      let read=0;
      const snapshot=step=>{
        const queries=name==='Registers' ? [['read',['a','b'],'number?'],['read',['a','c'],'number?'],['read',['missing','key'],'number?'],['counter',['k','r'],'number'],['counter',['k','other'],'number']] :
          nodes.flatMap(node=>[['parent',[node],'string?'],['root',[node],'string'],['childList',[node],'strings']]);
        for (const [method,args,type] of queries) {
          results.push({ok:observe(state[method](...args))});
          const call=`(«${name}#${method}» state${step} ${args.map(argument).join(' ')})`;
          const value=type==='number?' ? `((${call}.map (fun n=>Value.number (Float.Model.ofInt n))).getD .undefined, {})` :
            type==='number' ? `(.number (Float.Model.ofInt ${call}), {})` : type==='string?' ? `((${call}.map Value.string).getD .undefined, {})` :
            type==='string' ? `(.string ${call}, {})` : `(.ref 0, {heap := [.array (${call}.map Value.string)]})`;
          nativeResults.push(`observeResult (.ok ${value})`);
          model += `  let (result${read},state) ← apply ${ns}.program 10000 state (.method location "${method}") [${args.map(scalar)}]\n  let observed${read} := observeResult (.ok (result${read},state))\n`;
          modelResults.push(`observed${read}`); read++;
        }
      };
      snapshot(0);
      for (const [j,[method,...args]] of ops.entries()) {
        state[method](...args);
        const nativeArgs=args.map((value,k)=>name==='Tree' && method==='move' && k===1 ? value===undefined ? 'none' : `(some ${argument(value)})` : argument(value));
        const safe=`decide («${name}#${method}».safe state${j} ${nativeArgs.join(' ')})`;
        nativeResults.push(`Lean.toJson (${safe})`);
        results.push(true);
        native += `  let state${j+1} := («${name}#${method}» state${j} ${nativeArgs.join(' ')}).2.1\n`;
        model += `  let (_,state) ← apply ${ns}.program 10000 state (.method location "${method}") [${args.map(scalar)}]\n`;
        modelResults.push('Lean.toJson true');
        snapshot(j+1);
      }
      native+=`  return [${nativeResults}]\n#eval IO.println (Lean.Json.arr native${i}.toArray).compress\n`;
      model+=`  return [${modelResults}]\n#eval IO.println (match model${i} with | .ok results => (Lean.Json.arr results.toArray).compress | .error e => reprStr e)\n`;
      runner+=native+model;
      expected.push(results,results);
      traceCount++;
    }
    runner+=`end ${name}Traces\n`;
  }
  const file=resolve(dir,'Compare.lean');await writeFile(file,runner);
  const result=spawnSync('lake',['env','lean',file],{encoding:'utf8',timeout:180000,maxBuffer:16e6});
  assert.equal(result.status,0,result.stdout+result.stderr);
  assert.deepEqual(result.stdout.trim().split('\n').map(JSON.parse),expected);
  console.log(`Original shallow references passed: ${decisionCases.length} decision inputs and ${traceCount} class traces, with safety checks and intermediate-state observations.`);
} finally {await rm(dir,{recursive:true,force:true});}
