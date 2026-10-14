// Test-only harness: cross-checks the trusted parser and converter (Ariadne/Parse, Ariadne/Front/Convert.lean)
// against the TypeScript compiler. An independent converter below maps the compiler's syntax tree to the
// model's syntax, following the mapping documented in Convert.lean; for every file Ariadne accepts, both
// must give the same program (`ariadne ast`). Then random expressions, dense in operators, parentheses,
// literals and escapes, are compared the same way: a precedence, associativity or literal bug in either
// parser shows up as a difference.
import ts from 'typescript';
import { readdir, readFile, writeFile, mkdtemp } from 'node:fs/promises';
import { spawnSync } from 'node:child_process';
import { resolve, join } from 'node:path';
import { tmpdir } from 'node:os';
import { units } from './observe.mjs';

const cli = resolve('.lake/build/bin/ariadne');
const K = ts.SyntaxKind;

class Refused extends Error {}
const refuse = (node, what) => { throw new Refused(`${what ?? K[node.kind]}`); };

// ---------------------------------------------------------------------------
// Expressions

const binOps = {
  [K.PlusToken]: 'add', [K.MinusToken]: 'sub', [K.AsteriskToken]: 'mul', [K.SlashToken]: 'div',
  [K.PercentToken]: 'mod', [K.EqualsEqualsEqualsToken]: 'eq', [K.ExclamationEqualsEqualsToken]: 'ne',
  [K.LessThanToken]: 'lt', [K.LessThanEqualsToken]: 'le', [K.GreaterThanToken]: 'gt',
  [K.GreaterThanEqualsToken]: 'ge', [K.AmpersandAmpersandToken]: 'and', [K.BarBarToken]: 'or',
  [K.QuestionQuestionToken]: 'coalesce', [K.EqualsEqualsToken]: 'looseEq', [K.ExclamationEqualsToken]: 'looseNe',
};

/** A decimal literal's value if it is a safe integer (as `integerLiteral` decides). */
function numberLiteral(node) {
  const text = node.text;
  if (!/^[0-9]+(\.[0-9]*)?([eE][+-]?[0-9]+)?$/.test(text) && !/^\.[0-9]+/.test(text)) refuse(node, 'number syntax');
  const m = text.match(/^([0-9]*)(?:\.([0-9]*))?(?:[eE]([+-]?[0-9]+))?$/);
  const digits = (m[1] ?? '') + (m[2] ?? '');
  let exponent = BigInt(m[3] ?? '0') - BigInt((m[2] ?? '').length);
  let mantissa = BigInt(digits === '' ? '0' : digits);
  let value;
  if (exponent >= 0n) value = mantissa * 10n ** exponent;
  else if (mantissa % 10n ** -exponent === 0n) value = mantissa / 10n ** -exponent;
  else refuse(node, 'a non-integer literal');
  if (value > 2n ** 53n - 1n) refuse(node, 'an unsafe literal');
  return value.toString();
}

const isThis = n => n.kind === K.ThisKeyword;
const isThisField = n => ts.isPropertyAccessExpression(n) && isThis(n.expression);

function expr(n) {
  switch (n.kind) {
    case K.ParenthesizedExpression: return expr(n.expression);
    case K.NumericLiteral: return ['lit', ['number', numberLiteral(n)]];
    case K.BigIntLiteral: return ['lit', ['bigint', BigInt(n.text.slice(0, -1)).toString()]];
    case K.StringLiteral: case K.NoSubstitutionTemplateLiteral:
      if (n.kind === K.NoSubstitutionTemplateLiteral) refuse(n, 'a template literal');
      return ['lit', ['string', units(n.text)]];
    case K.TrueKeyword: return ['lit', ['bool', true]];
    case K.FalseKeyword: return ['lit', ['bool', false]];
    case K.NullKeyword: return ['lit', ['null']];
    case K.Identifier: return n.text === 'undefined' ? ['lit', ['undefined']] : ['var', n.text];
    case K.ThisKeyword: return ['var', 'this'];
    case K.PrefixUnaryExpression:
      if (n.operator === K.ExclamationToken) return ['unary', 'not', expr(n.operand)];
      if (n.operator === K.MinusToken) return ['unary', 'neg', expr(n.operand)];
      return refuse(n, 'a prefix operator');
    case K.BinaryExpression: {
      const op = binOps[n.operatorToken.kind];
      if (!op) refuse(n, `operator ${ts.tokenToString(n.operatorToken.kind)}`);
      return ['binary', op, expr(n.left), expr(n.right)];
    }
    case K.ConditionalExpression: return ['cond', expr(n.condition), expr(n.whenTrue), expr(n.whenFalse)];
    case K.CallExpression: {
      const f = n.expression;
      const args = n.arguments.map(expr);
      if (ts.isIdentifier(f)) return ['call', f.text, args];
      if (ts.isPropertyAccessExpression(f)) {
        const m = f.name.text;
        if (isThisField(f.expression) && (m === 'get' || m === 'has') && n.arguments.length === 1)
          return [m === 'get' ? 'stateGet' : 'stateHas', f.expression.name.text, args[0]];
        if (isThis(f.expression)) return ['callThis', m, args];
        if (ts.isIdentifier(f.expression) && f.expression.text === 'Math' && m === 'floor' && n.arguments.length === 1) {
          let a = n.arguments[0];
          while (ts.isParenthesizedExpression(a)) a = a.expression;
          if (ts.isBinaryExpression(a) && a.operatorToken.kind === K.SlashToken)
            return ['binary', 'floorDiv', expr(a.left), expr(a.right)];
        }
        return ['method', expr(f.expression), m, args];
      }
      return refuse(n, 'this call');
    }
    case K.PropertyAccessExpression:
      if (isThisField(n.expression) && n.name.text === 'size') return ['stateSize', n.expression.name.text];
      return ['field', expr(n.expression), n.name.text];
    case K.ElementAccessExpression: return ['index', expr(n.expression), expr(n.argumentExpression)];
    case K.ArrayLiteralExpression:
      return ['array', n.elements.map(e => {
        if (ts.isSpreadElement(e)) {
          const s = e.expression;
          if (ts.isCallExpression(s) && ts.isPropertyAccessExpression(s.expression) && isThisField(s.expression.expression) &&
              s.arguments.length === 0 && (s.expression.name.text === 'keys' || s.expression.name.text === 'values'))
            return [true, [s.expression.name.text === 'keys' ? 'stateKeys' : 'stateValues', s.expression.expression.name.text]];
          return [true, expr(s)];
        }
        return [false, expr(e)];
      })];
    case K.ObjectLiteralExpression:
      return ['record', n.properties.map(p => {
        if (ts.isPropertyAssignment(p)) return [propName(p.name), expr(p.initializer)];
        if (ts.isShorthandPropertyAssignment(p)) return [p.name.text, ['var', p.name.text]];
        if (ts.isSpreadAssignment(p)) return [null, expr(p.expression)];
        return refuse(p, 'this object member');
      })];
    case K.ArrowFunction:
      if (ts.isBlock(n.body)) refuse(n, 'a block-bodied arrow');
      return ['arrow', n.parameters.map(p => p.name.text), expr(n.body)];
    case K.NewExpression:
      if (ts.isIdentifier(n.expression) && n.expression.text === 'Map' && (n.arguments ?? []).length === 0) return ['newMap'];
      return refuse(n, 'new');
    default: return refuse(n);
  }
}

function propName(name) {
  if (ts.isIdentifier(name) || ts.isStringLiteral(name)) return name.text;
  return refuse(name, 'a computed property name');
}

// ---------------------------------------------------------------------------
// Statements

const branch = s => (ts.isBlock(s) ? s.statements.map(stmt) : [stmt(s)]);

function compound(target, op, rhs) {
  if (!ts.isIdentifier(target)) refuse(target, 'a compound assignment to a non-variable');
  return ['assign', target.text, ['binary', op, ['var', target.text], rhs]];
}

function stmt(s) {
  switch (s.kind) {
    case K.VariableStatement: {
      const list = s.declarationList;
      if (list.declarations.length !== 1) refuse(s, 'several declarations');
      const d = list.declarations[0];
      const kind = list.flags & ts.NodeFlags.Const ? 'const' : list.flags & ts.NodeFlags.Let ? 'let' : refuse(s, 'var');
      return [kind, d.name.text, expr(d.initializer)];
    }
    case K.ReturnStatement: return ['ret', s.expression ? expr(s.expression) : ['lit', ['undefined']]];
    case K.IfStatement: return ['ite', expr(s.expression), branch(s.thenStatement), s.elseStatement ? branch(s.elseStatement) : []];
    case K.Block: return ['block', s.statements.map(stmt)];
    case K.BreakStatement: return ['break'];
    case K.ContinueStatement: return ['continue'];
    case K.SwitchStatement:
      return ['switch', expr(s.expression), s.caseBlock.clauses.map(c =>
        [ts.isCaseClause(c) ? expr(c.expression) : null, c.statements.map(stmt)])];
    case K.WhileStatement: return ['while', expr(s.expression), branch(s.statement)];
    case K.ForOfStatement: {
      const d = s.initializer.declarations[0];
      if (ts.isArrayBindingPattern(d.name)) {
        const [i, x] = d.name.elements.map(e => e.name.text);
        const e = s.expression;
        return ['forEntries', i, x, expr(e.expression.expression), s.statement.statements.map(stmt)];
      }
      return ['forOf', d.name.text, expr(s.expression), branch(s.statement)];
    }
    case K.ForStatement: {
      const i = s.initializer.declarations[0].name.text;
      return ['forRange', i, s.condition.right.text, branch(s.statement)];
    }
    case K.ExpressionStatement: {
      const e = s.expression;
      if (ts.isBinaryExpression(e)) {
        const t = e.operatorToken.kind;
        if (t === K.EqualsToken) {
          if (!ts.isIdentifier(e.left)) refuse(e, 'an assignment to a non-variable');
          return ['assign', e.left.text, expr(e.right)];
        }
        const op = { [K.PlusEqualsToken]: 'add', [K.MinusEqualsToken]: 'sub', [K.AsteriskEqualsToken]: 'mul',
          [K.SlashEqualsToken]: 'div' }[t];
        if (op) return compound(e.left, op, expr(e.right));
      }
      if (ts.isPostfixUnaryExpression(e))
        return compound(e.operand, e.operator === K.PlusPlusToken ? 'add' : 'sub', ['lit', ['number', '1']]);
      if (ts.isCallExpression(e) && ts.isPropertyAccessExpression(e.expression)) {
        const f = e.expression;
        if (isThisField(f.expression) && f.name.text === 'set' && e.arguments.length === 2)
          return ['stateSet', f.expression.name.text, expr(e.arguments[0]), expr(e.arguments[1])];
        if (isThisField(f.expression) && f.name.text === 'delete' && e.arguments.length === 1)
          return ['stateDelete', f.expression.name.text, expr(e.arguments[0])];
        if (isThis(f.expression)) return ['callThisStmt', f.name.text, e.arguments.map(expr)];
      }
      return refuse(s, 'this expression statement');
    }
    default: return refuse(s);
  }
}

// ---------------------------------------------------------------------------
// Programs

function program(text, path) {
  const sf = ts.createSourceFile(path, text, ts.ScriptTarget.Latest, true, ts.ScriptKind.TS);
  if (sf.parseDiagnostics.length > 0) refuse(sf, `a syntax error: ${ts.flattenDiagnosticMessageText(sf.parseDiagnostics[0].messageText, ' ')}`);
  const fns = [];
  for (const s of sf.statements) {
    if (ts.isFunctionDeclaration(s)) {
      fns.push({ name: s.name.text, params: s.parameters.map(p => p.name.text), method: false, body: s.body.statements.map(stmt) });
    } else if (ts.isClassDeclaration(s)) {
      const fields = s.members.filter(ts.isPropertyDeclaration).map(m => m.name.text);
      fns.push({ name: `new ${s.name.text}`, params: [], method: false,
        body: [['ret', ['record', fields.map(f => [f, ['newMap']])]]] });
      for (const m of s.members.filter(ts.isMethodDeclaration)) {
        const body = m.body.statements.map(stmt);
        if (m.type && m.type.kind === K.VoidKeyword) body.push(['ret', ['lit', ['undefined']]]);
        fns.push({ name: m.name.text, params: ['this', ...m.parameters.map(p => p.name.text)], method: true, body });
      }
    } else if (!ts.isTypeAliasDeclaration(s) && !ts.isInterfaceDeclaration(s)) {
      refuse(s, 'a top-level statement');
    }
  }
  return fns;
}

/** A canonical form: JSON with object keys sorted, functions sorted by name (the model finds them by name). */
const canon = fns => JSON.stringify(
  [...fns].sort((a, b) => (a.name < b.name ? -1 : 1)).map(f => ({ body: f.body, method: f.method, name: f.name, params: f.params })));

function ariadneAst(path) {
  const run = spawnSync(cli, ['ast', path], { encoding: 'utf8' });
  if (run.status !== 0) return null;
  return JSON.parse(run.stdout);
}

let compared = 0;
let failures = 0;

async function check(path, label) {
  const text = await readFile(path, 'utf8');
  const ours = ariadneAst(path);
  let theirs;
  try { theirs = program(text, path); } catch (e) {
    if (!(e instanceof Refused)) throw e;
    if (ours !== null) { failures++; console.error(`${label}: Ariadne accepts what the cross-check refuses (${e.message})`); }
    return;
  }
  if (ours === null) return; // Ariadne refuses: nothing to compare.
  compared++;
  if (canon(ours) !== canon(theirs)) {
    failures++;
    console.error(`${label}: the programs differ\n  ariadne    ${canon(ours).slice(0, 2000)}\n  typescript ${canon(theirs).slice(0, 2000)}`);
  }
}

// Every TypeScript file of the tests.
for (const dir of ['Tests/fixtures', 'Tests/model', 'Tests/negative', ...process.argv.slice(2)]) {
  for (const f of (await readdir(dir)).filter(f => f.endsWith('.ts')).sort()) await check(resolve(dir, f), `${dir}/${f}`);
}
const files = compared;

// Random expressions.
let seed = 0x9e3779b9;
const random = () => ((seed = (Math.imul(seed ^ (seed >>> 15), 0x2c1b3c6d) + 0x6d2b79f5) >>> 0) / 2 ** 32);
const pick = xs => xs[Math.floor(random() * xs.length)];
const binary = ['+', '-', '*', '%', '<', '<=', '>', '>=', '===', '!==', '&&', '||', '??', '==', '!='];
const strings = ['""', '"a"', "'b'", '"\\n"', '"\\u00e9"', '"\\u{1F600}"', '"\\x41"', '"\\\\"', "'\\''", '"\\0"', '"\\t\\r"'];
const numbers = ['0', '1', '42', '9007199254740991', '1e3', '2.50e1', '0.0', '100', '7'];
function gen(depth) {
  if (depth === 0 || random() < 0.2) {
    return pick([() => pick(['a', 'b', 'c', 'xs', 'undefined', 'null', 'true', 'false']), () => pick(numbers),
      () => pick(strings), () => `${pick(numbers)}n`])();
  }
  switch (Math.floor(random() * 10)) {
    case 0: return `(${gen(depth - 1)})`;
    case 1: return `!${gen(depth - 1)}`;
    case 2: return `-${gen(depth - 1)}`;
    case 3: return `${gen(depth - 1)} ? ${gen(depth - 1)} : ${gen(depth - 1)}`;
    case 4: return `${pick(['a', 'xs', 'r'])}.${pick(['length', 'f', 'g'])}`;
    case 5: return `f(${gen(depth - 1)}, ${gen(depth - 1)})`;
    case 6: return `[${gen(depth - 1)}, ...${pick(['xs', 'ys'])}]`;
    case 7: return `{ k: ${gen(depth - 1)}, ...r }`;
    case 8: return `xs.map((y) => ${gen(depth - 1)})`;
    default: return `${gen(depth - 1)} ${pick(binary)} ${gen(depth - 1)}`;
  }
}
const dir = await mkdtemp(join(tmpdir(), 'ariadne-cross-'));
const rounds = Number(process.env.CROSSCHECK_ROUNDS ?? 1500);
for (let k = 0; k < rounds; k++) {
  const body = Array.from({ length: 4 }, () => `  const v${k}_${Math.floor(random() * 1e6)} = ${gen(4)};`).join('\n');
  const text = `export function f(a: number, b: number, c: number): number {\n${body}\n  return 0;\n}\n`;
  const path = join(dir, `e${k}.ts`);
  await writeFile(path, text);
  await check(path, `random ${k}: ${text}`);
}

if (failures > 0) { console.error(`Cross-check: ${failures} differences.`); process.exit(1); }
console.log(`Cross-check passed: ${files} files and ${compared - files} random programs parse alike.`);
