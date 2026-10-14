import Ariadne.Front.Convert
import Ariadne.Typed.Syntax

/-!
# Type checking and printing

Untrusted. Builds, as Lean source, the typed program whose erasure must equal the
converted AST, the readable definitions that must equal its denotation, and the
per-function source theorems. The kernel checks all of it when the generated file
is compiled, so a bug here makes that file fail to check; it cannot produce a
wrong theorem.
-/

namespace Ariadne.Front
open Ariadne.Parse (Diagnostic Checked Span)

def mismatch (span : Span) (message : String) : Checked α :=
  throw { code := "A2002", message, span }

def ident (x : String) : String := s!"«{x}»"

def leanString (s : String) : String := Id.run do
  let mut out := "\""
  for c in s.toList do
    out := out ++ match c with
      | '"' => "\\\"" | '\\' => "\\\\" | '\n' => "\\n" | '\t' => "\\t" | c => c.toString
  return out ++ "\""

/-- A JavaScript string literal: `js "…"` when every code unit is a printable BMP
character, else the code units. -/
def jsString (units : List UInt16) : String :=
  if units.all fun u => (u ≥ 0x20 && u < 0x7F) || (u ≥ 0xA0 && u < 0xD800) || (u ≥ 0xE000 && u < 0xFFFE) then
    s!"(js {leanString (String.ofList (units.map fun u => Char.ofNat u.toNat))})"
  else
    s!"({units.map fun u => s!"{u.toNat}"} : JSString)"

/-! ## Types -/

def printTag : TagLit → String
  | .str s => s!"(.str {jsString s})"
  | .bool b => s!"(.bool {b})"

def tagLitTS : TagLit → String
  | .str s => s!"'{String.ofList (s.map fun u => Char.ofNat u.toNat)}'"
  | .bool b => toString b

def printNullish : Nullish → String
  | .undef => ".undef" | .null => ".null" | .both => ".both"

mutual
  /-- Lean syntax for a type, naming the types `named` resolves. -/
  partial def printTyWith (named : Ty → Option String) (τ : Ty) : String :=
    match named τ with
    | some n => n
    | none => match τ with
      | .bool => ".bool" | .int => ".int" | .number => ".number" | .string => ".string"
      | .tag t => s!"(.tag {printTag t})"
      | .lits a as => s!"(.lits {jsString a} [{", ".intercalate (as.map jsString)}])"
      | .option n τ => s!"(.option {printNullish n} {printTyWith named τ})"
      | .record fs => s!"(.record {printFields named fs})"
      | .union key vs => s!"(.union {leanString key} {printVariants named vs})"
      | .array τ => s!"(.array {printTyWith named τ})"
      | .map τ => s!"(.map {printTyWith named τ})"

  partial def printFields (named : Ty → Option String) : Fields → String
    | .nil => ".nil"
    | .cons f τ rest => s!"(.cons {leanString f} {printTyWith named τ} {printFields named rest})"

  partial def printVariants (named : Ty → Option String) : Variants → String
    | .one t fs => s!"(.one {printTag t} {printFields named fs})"
    | .cons t fs rest => s!"(.cons {printTag t} {printFields named fs} {printVariants named rest})"
end

def printTy : Ty → String := printTyWith fun _ => none

def _root_.Ariadne.Ty.ts : Ty → String
  | .bool => "boolean" | .int => "bigint" | .number => "number" | .string => "string"
  | .tag t => tagLitTS t | .lits .. => "a string literal union" | .option .. => "an optional"
  | .record _ => "a record" | .union .. => "a union" | .array _ => "an array" | .map _ => "a Map"

/-- Named types (aliases and interfaces) and their resolved forms. -/
structure Types where
  aliases : List (String × Parse.Ty)
  /-- Resolved named types, printed as `ty.«Name»`. -/
  named : List (String × Ty) := []
  /-- Named types that also get a readable Lean name (an alias, field accessors, literal constants and
  variant constructors): those whose name no function or generated declaration uses. -/
  readable : List String := []

def Types.name (T : Types) (τ : Ty) : Option String := (T.named.find? (·.2 == τ)).map fun (n, _) => s!"ty.{ident n}"

def Types.print (T : Types) (τ : Ty) : String := printTyWith T.name τ

/-- A type as an argument: parenthesized unless it is one word. -/
def atomText (x : String) : String :=
  -- Already one parenthesized term: its first parenthesis closes at its end.
  let wrapped := x.startsWith "(" && Id.run do
    let mut depth := 0
    let cs := x.toList
    for (c, i) in cs.zipIdx do
      if c == '(' then depth := depth + 1
      else if c == ')' then
        depth := depth - 1
        if depth == 0 then return i + 1 == cs.length
    return false
  if wrapped || !x.contains ' ' then x else s!"({x})"

/-- The Lean type of a denoted value. -/
partial def Types.lean (T : Types) : Ty → String
  | .bool => "Bool" | .int => "Int" | .number => "Int" | .string => "JSString"
  | τ => match (T.named.find? (·.2 == τ)).map (·.1), τ with
    | some n, _ => if T.readable.contains n then ident n else s!"ty.{ident n}.denote"
    | none, .array σ => s!"List {atomText (T.lean σ)}"
    | none, .map σ => s!"List (JSString × {T.lean σ})"
    | none, .option _ σ => s!"Option {atomText (T.lean σ)}"
    | none, _ => s!"(({T.print τ} : Ty)).denote"

def Fields.toList : Fields → List (String × Ty)
  | .nil => []
  | .cons f τ rest => (f, τ) :: Fields.toList rest

/-- A literal's text as a Lean name, when it can be one. -/
def litName (units : List UInt16) : Option String :=
  if !units.isEmpty && units.all (fun u => (u ≥ 0x21 && u < 0x7F) && u != 0x60) then
    some (String.ofList (units.map fun u => Char.ofNat u.toNat))
  else none

def tagName : TagLit → Option String
  | .str s => litName s
  | .bool b => some (toString b)

/-- The readable name of a named type, if it has one. -/
def Types.nameOf? (T : Types) (τ : Ty) : Option String :=
  (T.named.find? (·.2 == τ)).bind fun (n, _) => if T.readable.contains n then some n else none

/-- The name of the setter of field `f`: `withF`. -/
def setterName (f : String) : String := "with" ++ f.capitalize

/-- Whether a record's constructor `mk` and setters `withF` clash with none of its fields. -/
def namesFree (fs : Fields) : Bool :=
  let names := (Fields.toList fs).map (·.1)
  !names.contains "mk" && names.all fun f => !names.contains (setterName f)

/-- The readable name of a record type whose fields can be read, built and set by name. -/
def Types.recordName? (T : Types) : Ty → Option String
  | τ@(.record fs) => if namesFree fs then T.nameOf? τ else none
  | _ => none

def Variants.toList : Variants → List (TagLit × Fields)
  | .one t fs => [(t, fs)]
  | .cons t fs rest => (t, fs) :: Variants.toList rest

/-- The constructors' names of a named union, when every variant has one (`«U».«tag»`). -/
def Types.ctorNames? (T : Types) (τ : Ty) : Option (List String) := do
  let .union _ vs := τ | none
  let n ← T.nameOf? τ
  (Variants.toList vs).mapM fun (t, _) => (tagName t).map fun tn => s!"{ident n}.{ident tn}"

/-- The payload type of a named union's variant `i` with fields, `«U».Variant.«tag»`. -/
def Types.payloadName? (T : Types) (τ : Ty) (i : Nat) : Option String := do
  let .union _ vs := τ | none
  let n ← T.nameOf? τ
  let (t, fs) ← (Variants.toList vs)[i]?
  if (Fields.toList fs).isEmpty then none
  let tn ← tagName t
  return s!"{ident n}.Variant.{ident tn}"

/-- The union (and variant index) a variant record `{key: tag, …fields}` belongs to, among the named types. -/
def Types.variantOf? (T : Types) (σ : Ty) : Option (Ty × Nat) :=
  T.named.findSome? fun (_, τ) => match τ with
    | .union key vs =>
      (Variants.toList vs).zipIdx.findSome? fun ((t, fs), i) =>
        if Ty.record (.cons key (.tag t) fs) == σ then some (τ, i) else none
    | _ => none

def Fields.ofList : List (String × Ty) → Fields
  | [] => .nil
  | (f, τ) :: rest => .cons f τ (Fields.ofList rest)

def Variants.ofList : List (TagLit × Fields) → Option Variants
  | [] => none
  | [(t, fs)] => some (.one t fs)
  | (t, fs) :: rest => (Variants.ofList rest).map (.cons t fs)

def unsupportedTy (span : Span) (what : String) : Checked α :=
  throw { code := "A1001", message := s!"{what} is outside the supported subset", span }

mutual
  /-- Union members, with aliases of unions expanded. -/
  partial def Types.members (T : Types) (span : Span) (fuel : Nat) : Parse.Ty → Checked (List Parse.Ty)
    | .union a b => return (← T.members span fuel a) ++ (← T.members span fuel b)
    | .fieldReadonly t => T.members span fuel t
    | t@(.named n) => match fuel, T.aliases.lookup n with
      | f + 1, some def_@(.union ..) => T.members span f def_
      | _, _ => pure [t]
    | t => pure [t]

  partial def Types.resolve (T : Types) (span : Span) (fuel : Nat) (t : Parse.Ty) : Checked Ty := do
    let fuel ← match fuel with
      | 0 => unsupportedTy span "a recursive type"
      | f + 1 => pure f
    let ms ← T.members span fuel t
    let nullish := ms.filter fun m => m matches .undefined | .null
    let rest := ms.filter fun m => !(m matches .undefined | .null)
    let core ← match rest with
      | [] => unsupportedTy span "a type of only nullish values"
      | [m] => T.single span fuel m
      | _ =>
        if rest.all (· matches .stringLiteral _) then
          let lits := rest.filterMap fun | .stringLiteral s => some s | _ => none
          pure (.lits lits.head! lits.tail)
        else T.recordUnion span fuel rest
    if nullish.isEmpty then return core
    let hasU := nullish.any (· matches .undefined)
    let hasN := nullish.any (· matches .null)
    if core matches .option .. then unsupportedTy span "a nested optional"
    return .option (if hasU && hasN then .both else if hasN then .null else .undef) core

  partial def Types.single (T : Types) (span : Span) (fuel : Nat) : Parse.Ty → Checked Ty
    | .boolean => pure .bool
    | .bigint => pure .int
    | .number => pure .number
    | .string => pure .string
    | .stringLiteral s => pure (.tag (.str s))
    | .named "true" => pure (.tag (.bool true))
    | .named "false" => pure (.tag (.bool false))
    | .named n => match T.aliases.lookup n with
      | some def_ => T.resolve span fuel def_
      | none => unsupportedTy span s!"the type '{n}'"
    | .fieldReadonly t => T.resolve span fuel t
    | .record fields => return .record (Fields.ofList (← fields.mapM fun (f, t) => return (f, ← T.resolve span fuel t)))
    | .array t | .readonly (.array t) => return .array (← T.resolve span fuel t)
    | _ => unsupportedTy span "this type"

  /-- A union of records told apart by a literal field. -/
  partial def Types.recordUnion (T : Types) (span : Span) (fuel : Nat) (ms : List Parse.Ty) : Checked Ty := do
    let records ← ms.mapM fun m => do
      match ← T.resolve span fuel m with
      | .record fs => pure (Fields.toList fs)
      | _ => unsupportedTy span "a union of non-record types"
    let tagOf (fs : List (String × Ty)) (key : String) : Option TagLit :=
      match fs.lookup key with
      | some (.tag t) => some t
      | _ => none
    let key? := records.head!.map (·.1) |>.find? fun k => records.all fun fs => (tagOf fs k).isSome
    let some key := key? | unsupportedTy span "a union of records without a common literal field"
    let variants := records.map fun fs => ((tagOf fs key).get!, Fields.ofList (fs.filter (·.1 != key)))
    let some vs := Variants.ofList variants | unsupportedTy span "an empty union"
    if !vs.tagsOk then unsupportedTy span "a union whose tags repeat or mix strings and booleans"
    return .union key vs
end

def Types.ofProgram (p : Parse.Program) : Checked Types := do
  let mut T : Types := { aliases := p.aliases }
  for (n, t) in p.aliases do
    let τ ← T.resolve {} 64 t
    T := { T with named := T.named ++ [(n, τ)] }
  return T

def Types.param (T : Types) (p : Parse.Param) : Checked Ty := T.resolve p.span 64 p.ty

/-! ## Scopes -/

structure FnSig where
  name : String
  params : List (String × Ty)
  result : Ty
  /-- The body is trivially safe (no operation that can leave the model). -/
  trivial : Bool := true
  /-- A method (its first parameter is `this`), and whether it changes the state. -/
  method : Bool := false
  void : Bool := false
  deriving Inhabited

/-- How a variable a `switch` narrowed to a variant is bound in readable definitions: to nothing (a variant
without fields), to its one field, or to its payload (the variant's fields after the tag). -/
inductive PKind where
  | unit | single | multi
  deriving BEq, Inhabited

/-- A variant record's value, `((), payload)`, given by its payload: `text` is the payload, or for a
variant with one field that field's value. -/
structure Payload where
  kind : PKind
  text : String
  deriving Inhabited

def Payload.whole (p : Payload) : String :=
  match p.kind with
  | .unit => "()"
  | .single => s!"({p.text}, ())"
  | .multi => p.text

structure Scope where
  /-- Variables bound to their variant's payload (see `PKind`). -/
  payloads : List (String × PKind) := []
  fns : List FnSig
  /-- Bindings in scope, innermost first, with their current (narrowed) types. -/
  locals : List (String × Ty)
  /-- The assignable bindings: parameters and `let` declarations. -/
  mutables : List String := []
  /-- In a method that changes the state (`return;` gives the state). -/
  void : Bool := false

/-- A variable reference past the bindings `skipped` (innermost first). Each step
cites a named lemma `ne.«x».«y»` (emitted by `printFile`): a postponed `by decide`
there would block reducing narrowed contexts during elaboration. -/
def varPathN (x : String) : List String → String
  | [] => ".here"
  | y :: ys => s!"(.there ne.{ident x}.{ident y} {varPathN x ys})"

/-- The `ne.«x».«y»` lemmas a generated text cites. -/
def collectNe (text : String) : List (String × String) :=
  ((text.splitOn "ne.«").drop 1).filterMap fun p =>
    match p.splitOn "».«" with
    | a :: rest :: _ => some (a, (rest.splitOn "»").head!)
    | _ => none

def fnPath : Nat → String
  | 0 => ".here"
  | n + 1 => s!"(.there {fnPath n})"

def fidxPath : Nat → String
  | 0 => ".here"
  | n + 1 => s!"(.there {fidxPath n})"

/-- The `VIdx` of variant `i` of `n`. -/
def vidxPath (i n : Nat) : String :=
  match i with
  | 0 => if n == 1 then ".one" else ".head"
  | k + 1 => s!"(.there {vidxPath k (n - 1)})"

/-- Readable injection of variant `i` of `n` into the union's sum. -/
def injText (i n : Nat) (x : String) : String :=
  match i with
  | 0 => if n == 1 then x else s!"(Sum.inl {x})"
  | k + 1 => s!"(Sum.inr {injText k (n - 1) x})"

/-- Readable projection of field `k` of a record tuple. -/
def projText (e : String) (k : Nat) : String :=
  e ++ String.join (List.replicate k ".2") ++ ".1"

def Scope.lookup (s : Scope) (x : String) : Option (Nat × Ty) :=
  match s.locals.findIdx? (·.1 == x) with
  | some i => some (i, s.locals[i]!.2)
  | none => none

def Scope.varPath (s : Scope) (i : Nat) : String :=
  varPathN s.locals[i]!.1 ((s.locals.take i).map (·.1))

def Scope.narrow (s : Scope) (i : Nat) (σ : Ty) : Scope :=
  { s with locals := s.locals.set i (s.locals[i]!.1, σ) }

/-! ## Expressions -/

/-- A checked expression as typed syntax, and as a readable Lean term, with its
safety condition (meaningful when it is not trivially safe; parents leave out
trivially safe subterms, as `TExpr.safe` does). -/
structure Out where
  ty : Ty
  typed : String
  readable : String
  atomic : Bool := false
  trivial : Bool := true
  safe : String := "true"
  /-- For a variant record's value, its payload. -/
  payload : Option Payload := none
  /-- For a record literal, its fields' terms, in order. -/
  fieldTerms : List String := []
  deriving Inhabited

def Out.term (o : Out) : String := if o.atomic then o.readable else s!"({o.readable})"

/-- Parenthesize an operand of `&&` unless precedence makes it unnecessary. -/
def paren (t : String) : String :=
  let needs := ["if ", "match ", "let ", "fun "].any (fun p => t.startsWith p) ||
    ["\n", "&&", "||", "=>"].any (fun p => (t.splitOn p).length > 1)
  if needs then s!"({t})" else t

/-- Readable `andT`. -/
def andTText (ta : Bool) (a : String) (tb : Bool) (b : String) : String :=
  if ta then (if tb then "true" else b) else if tb then a else s!"{paren a} && {paren b}"

/-- Readable `t || a` for a static `t`. -/
def orTText (t : Bool) (a : String) : String := if t then "true" else a

/-- Readable `a && b` where `a` may be the literal `true` (which reduces away). -/
def andText (a b : String) : String := if a == "true" then b else s!"{paren a} && {paren b}"

/-- A subterm's safety as its parent consults it. -/
def Out.ok (o : Out) : String := orTText o.trivial o.safe

/-- Two operands, both evaluated. -/
def both (a b : Out) : String := andTText a.trivial a.safe b.trivial b.safe

/-- A variable narrowed by a test, with how its narrowed value re-embeds. -/
structure Narrowed where
  index : Nat
  name : String
  wide : Ty
  narrow : Ty
  /-- Readable re-embedding of the narrowed value named `«x»`. -/
  embed : String

/-- The continuation `k` after re-embedding the narrowed variable, when `k` uses it. -/
def Narrowed.wrap (n : Narrowed) (k : String → String) : String → String :=
  fun i =>
    let rest := k i
    if n.embed != ident n.name && (rest.splitOn (ident n.name)).length > 1 then
      s!"let {ident n.name} := {n.embed}\n{i}{rest}"
    else rest

def vrec' (key : String) (t : TagLit) (fs : Fields) : Ty := .record (.cons key (.tag t) fs)

/-- Readable `this` with field `j` (of `n`) replaced. -/
def tupleSetText (e : String) (j n : Nat) (v : String) : String :=
  let before := (List.range j).map (projText e)
  let _ := n
  "(" ++ ", ".intercalate (before ++ [v, e ++ String.join (List.replicate (j + 1) ".2")]) ++ ")"

/-- Readable read of field `k` of a value `e` (atomic) of record type `τ`: by name when the record has one. -/
def Types.fieldText (T : Types) (τ : Ty) (e : String) (k : Nat) : String :=
  match T.nameOf? τ, τ with
  | some _, .record fs => s!"{e}.{ident (Fields.toList fs)[k]!.1}"
  | _, _ => projText e k

/-- Readable `e` (atomic) of record type `τ` with field `k` set to `v`. -/
def Types.setText (T : Types) (τ : Ty) (e : String) (k : Nat) (v : String) : String :=
  match T.recordName? τ, τ with
  | some _, .record fs => s!"{e}.{ident (setterName (Fields.toList fs)[k]!.1)} {atomText v}"
  | _, .record fs => tupleSetText e k (Fields.toList fs).length v
  | _, _ => tupleSetText e k 0 v

/-- Readable read of field `k` of a variant record `σ` given by its payload (field 0 is the tag). -/
def Types.payloadField (T : Types) (σ : Ty) (p : Payload) (k : Nat) : String :=
  if k == 0 then "()" else
  match p.kind, σ with
  | .single, _ => p.text
  | .multi, .record (.cons _ _ fs) =>
    let named := (T.variantOf? σ).bind fun (u, i) => T.payloadName? u i
    if named.isSome then s!"{p.text}.{ident (Fields.toList fs)[k - 1]!.1}" else projText p.text (k - 1)
  | _, _ => "()"

/-- Readable injection of variant `i` of the union `τ`, given by its payload. -/
def Types.injectText (T : Types) (τ : Ty) (i : Nat) (p : Payload) : String :=
  match (T.ctorNames? τ).bind (·[i]?), τ with
  | some c, _ => if p.kind == .unit then c else s!"({c} {atomText p.text})"
  | none, .union _ vs => injText i (Variants.toList vs).length p.whole
  | none, _ => p.whole

/-- The payload of a variant record's readable value `e` (atomic), for variant `i` of `τ`. -/
def payloadOf (τ : Ty) (i : Nat) (e : String) : Payload :=
  match τ with
  | .union _ vs => match ((Variants.toList vs)[i]?.map (Fields.toList ·.2)).getD [] with
    | [] => { kind := .unit, text := "()" }
    | [_] => { kind := .single, text := s!"{e}.2.1" }
    | _ => { kind := .multi, text := s!"{e}.2" }
  | _ => { kind := .multi, text := s!"{e}.2" }

/-- Use a value of type `out.ty` at type `τ`: equal, or a no-op embedding. -/
def coerce (T : Types) (span : Span) (out : Out) (τ : Ty) : Checked Out := do
  if out.ty == τ then return out
  match τ with
  | .option n σ =>
    if out.ty == σ then
      return { ty := τ, typed := s!"(.widen (.some {printNullish n} {T.print σ}) {out.typed})",
               readable := s!"some {out.term}", trivial := out.trivial, safe := out.safe }
    mismatch span s!"{out.ty.ts} where {τ.ts} is expected"
  | .union key vs =>
    let variants := Variants.toList vs
    match variants.findIdx? (fun (t, fs) => out.ty == vrec' key t fs) with
    | some i =>
      let p := out.payload.getD (payloadOf τ i out.term)
      return { ty := τ, typed := s!"(.widen (.variant {vidxPath i variants.length}) {out.typed})",
               readable := T.injectText τ i p, atomic := true, trivial := out.trivial, safe := out.safe }
    | none => mismatch span s!"{out.ty.ts} where {τ.ts} is expected"
  | _ => mismatch span s!"{out.ty.ts} where {τ.ts} is expected"

def nullTestVar : Parse.Expr → Option (String × Bool)
  | .binary "==" (.var x _) (.literal .null _) _ => some (x, true)
  | .binary "!=" (.var x _) (.literal .null _) _ => some (x, false)
  | _ => none

/-- The narrowing a `x == null` / `x != null` test establishes on an optional local. -/
def Scope.nullNarrowing (s : Scope) (span : Span) (x : String) : Checked (Narrowed × String) := do
  match s.lookup x with
  | some (i, τ@(.option _ σ)) =>
    if !σ.nonNullish then mismatch span "a nested optional"
    return ({ index := i, name := x, wide := τ, narrow := σ, embed := s!"some {ident x}" }, s.varPath i)
  | some _ => mismatch span s!"'{x}' is not optional"
  | none => throw { code := "A2001", message := s!"unknown variable '{x}'", span }

def protoName (f : String) : Bool := protoNames.contains f

def declare (s : Scope) (span : Span) (x : String) (τ : Ty) : Checked Scope := do
  if x == "this" || s.locals.any (·.1 == x) || s.fns.any (fun f => f.name == x && !f.method) then
    throw { code := "A2004", message := s!"'{x}' shadows a declaration in scope", span,
            help := some "Rename it: the model requires names in scope to be distinct." }
  pure { s with locals := (x, τ) :: s.locals }

/-- `a.trivial`/`a.safe` of a right-nested list (`TArgs`, `TEntries`, `TElems`). -/
def foldSafe (outs : List Out) : Bool × String :=
  outs.foldr (fun o (t, txt) => (o.trivial && t, andTText o.trivial o.safe t txt)) (true, "true")

/-- A readable array literal: `[a, b]` is `a :: b :: []`, a spread `xs ++ rest`. -/
partial def elemsText (es : List (Bool × String)) : String :=
  let plain := es.takeWhile (!·.1)
  match es.dropWhile (!·.1) with
  | [] => "[" ++ ", ".intercalate (plain.map (·.2)) ++ "]"
  | (_, xs) :: rest =>
    let tail := s!"{xs} ++ ({elemsText rest})"
    if plain.isEmpty then tail else s!"{" :: ".intercalate (plain.map (·.2))} :: ({tail})"

/-- A checked callback: typed syntax, the readable function and its safety function. -/
structure Fn where
  typed : String
  lam : String
  lamSafe : String
  trivial : Bool
  ty : Ty

/-- A declared function used as a value: its `FVar` path and signature. -/
def Scope.fnRef (s : Scope) (span : Span) (f : String) : Checked (String × FnSig) := do
  if s.locals.any (·.1 == f) then mismatch span s!"'{f}' is a local, not a declared function"
  let some j := s.fns.findIdx? (fun g => g.name == f && !g.method)
    | throw { code := "A2001", message := s!"'{f}' is not a function declared earlier", span }
  return (fnPath (s.fns.length - 1 - j), s.fns[j]!)

/-- The state (`this`) of the method being checked: its path, record fields, and
the field `f` (a map) with its index and value type. -/
def Scope.stateField (s : Scope) (span : Span) (f : String) : Checked (String × Fields × Nat × Ty) := do
  let some (i, .record fs) := s.lookup "this" | mismatch span "'this' outside a method"
  let fields := Fields.toList fs
  let some j := fields.findIdx? (·.1 == f) | mismatch span s!"no field '{f}'"
  let .map τ := fields[j]!.2 | mismatch span s!"field '{f}' is not a Map"
  return (s.varPath i, fs, j, τ)

/-- A method of the class, by name: its `FVar` path and signature. -/
def Scope.methodRef (s : Scope) (span : Span) (m : String) : Checked (String × FnSig) := do
  let some j := s.fns.findIdx? (fun g => g.name == m && g.method)
    | throw { code := "A2001", message := s!"'{m}' is not a method declared earlier (or it calls itself)", span }
  return (fnPath (s.fns.length - 1 - j), s.fns[j]!)

mutual
  partial def checkExpr (T : Types) (s : Scope) (e : Parse.Expr) (expected : Option Ty) : Checked Out := do
    let out ← inferExpr T s e expected
    match expected with
    | some τ => coerce T e.span out τ
    | none => pure out

  partial def inferExpr (T : Types) (s : Scope) (e : Parse.Expr) (expected : Option Ty) : Checked Out := do
    match e with
    | .literal (.boolean b) _ =>
      if expected == some (.tag (.bool b)) then
        return { ty := .tag (.bool b), typed := s!"(.tagLit (.bool {b}))", readable := "()", atomic := true }
      return { ty := .bool, typed := s!"(.bool {b})", readable := s!"{b}", atomic := true }
    | .literal (.bigint n) _ =>
      return { ty := .int, typed := s!"(.int {n})", readable := s!"({n} : Int)", atomic := true }
    | .literal (.number m ex) span => do
      let n ← integerLiteral span m ex
      return { ty := .number, typed := s!"(.num {n})", readable := s!"({n} : Int)", atomic := true }
    | .literal (.string units) _ =>
      match expected with
      | some (.tag (.str u)) =>
        if u == units then
          return { ty := .tag (.str u), typed := s!"(.tagLit (.str {jsString u}))", readable := "()", atomic := true }
        return { ty := .string, typed := s!"(.str {jsString units})", readable := jsString units, atomic := true }
      | some τ@(.lits a as) =>
        match (a :: as).findIdx? (· == units) with
        | some i =>
          let readable := match T.nameOf? τ, litName units with
            | some n, some l => s!"{ident n}.{ident l}"
            | _, _ => s!"({i} : Fin {as.length + 1})"
          return { ty := τ, typed := s!"(.litIn {jsString a} [{", ".intercalate (as.map jsString)}] {i})",
                   readable, atomic := true }
        | none => mismatch e.span "a string outside the literal union"
      | _ => return { ty := .string, typed := s!"(.str {jsString units})", readable := jsString units, atomic := true }
    | .literal .undefined span =>
      match expected with
      | some τ@(.option n σ) =>
        if !n.undef? then mismatch span s!"undefined where {τ.ts} admits only null"
        return { ty := τ, typed := s!"(.undef {printNullish n} {T.print σ} (by decide +kernel))", readable := "none",
                 atomic := true }
      | _ => mismatch span "undefined needs an optional type here"
    | .literal .null span =>
      match expected with
      | some τ@(.option n σ) =>
        if !n.null? then mismatch span s!"null where {τ.ts} admits only undefined"
        return { ty := τ, typed := s!"(.null {printNullish n} {T.print σ} (by decide +kernel))", readable := "none",
                 atomic := true }
      | _ => mismatch span "null needs an optional type here"
    | .var "this" span => mismatch span "'this' used as a value (only this.f.get/has/size/set/delete and this.m())"
    | .var x span =>
      match s.lookup x with
      | some (i, τ) => match s.payloads.lookup x with
        | some kind =>
          let p : Payload := { kind, text := if kind == .unit then "()" else ident x }
          return { ty := τ, typed := s!"(.var {s.varPath i})", readable := s!"((), {p.whole})", atomic := true,
                   payload := some p }
        | none => return { ty := τ, typed := s!"(.var {s.varPath i})", readable := ident x, atomic := true }
      | none => throw { code := "A2001", message := s!"unknown variable '{x}'", span }
    | .unary "-" (.literal (.number m ex) _) span => do
      let n ← integerLiteral span m ex
      return { ty := .number, typed := s!"(.negNum {n} (by decide +kernel))", readable := s!"(-({n} : Int))", atomic := true }
    | .unary op a span => do
      let a ← inferExpr T s a none
      match op, a.ty with
      | "!", .bool => return { ty := .bool, typed := s!"(.not {a.typed})", readable := s!"!{a.term}",
                               trivial := a.trivial, safe := a.safe }
      | "-", .int => return { ty := .int, typed := s!"(.neg {a.typed})", readable := s!"(-{a.term})", atomic := true,
                              trivial := a.trivial, safe := a.safe }
      | "-", .number => return { ty := .number, typed := s!"(.nneg {a.typed})", readable := s!"(-{a.term})",
                                 atomic := true, trivial := false, safe := andText a.ok s!"Ariadne.inRange (-{a.term})" }
      | op, τ => mismatch span s!"'{op}' does not apply to {τ.ts}"
    | .binary op a b span => checkBinary T s op a b span expected
    | .conditional c a b span =>
      match nullTestVar c with
      | some (x, isNull) => do
        let (n, path) ← s.nullNarrowing span x
        let narrowed := s.narrow n.index n.narrow
        let (sa, sb) := if isNull then (s, narrowed) else (narrowed, s)
        let (a, b) ← checkBranches T sa a sb b expected
        let ctor := if isNull then "condNull" else "condNotNull"
        let arms (ra rb : String) := if isNull then
            s!"match {ident x} with | none => {ra} | some {ident x} => {rb}"
          else s!"match {ident x} with | some {ident x} => {ra} | none => {rb}"
        return { ty := a.ty, typed := s!"(.{ctor} {path} (by decide +kernel) {a.typed} {b.typed})",
                 readable := arms a.readable b.readable, trivial := a.trivial && b.trivial,
                 safe := arms (paren a.ok) (paren b.ok) }
      | none => do
        let c ← checkExpr T s c (some .bool)
        let (a, b) ← checkBranches T s a s b expected
        return { ty := a.ty, typed := s!"(.cond {c.typed} {a.typed} {b.typed})",
                 readable := s!"if {c.readable} then {a.readable} else {b.readable}",
                 trivial := c.trivial && a.trivial && b.trivial,
                 safe := andTText c.trivial c.safe (a.trivial && b.trivial)
                   s!"if {c.readable} then {paren a.ok} else {paren b.ok}" }
    | .call (.member (.member (.var "this" _) f _) "get" _) [k] span => do
      let (path, fsT, j, τ) ← s.stateField span f
      if !τ.nonNullish then mismatch span "a Map whose values may be undefined (get would be ambiguous)"
      let k ← checkExpr T s k (some .string)
      return { ty := .option .undef τ, typed := s!"(.stateGet {path} {fidxPath j} (by decide +kernel) {k.typed})",
               readable := s!"Ariadne.mapGet {T.fieldText (.record fsT) (ident "this") j} {k.term}", trivial := k.trivial, safe := k.safe }
    | .call (.member (.member (.var "this" _) f _) "has" _) [k] span => do
      let (path, fsT, j, _) ← s.stateField span f
      let k ← checkExpr T s k (some .string)
      return { ty := .bool, typed := s!"(.stateHas {path} {fidxPath j} {k.typed})",
               readable := s!"(Ariadne.mapGet {T.fieldText (.record fsT) (ident "this") j} {k.term}).isSome", trivial := k.trivial,
               safe := k.safe }
    | .member (.member (.var "this" _) f _) "size" span => do
      let (path, fsT, j, _) ← s.stateField span f
      return { ty := .number, typed := s!"(.stateSize {path} {fidxPath j})",
               readable := s!"(List.length {T.fieldText (.record fsT) (ident "this") j} : Int)", atomic := true }
    | .call (.member (.var "this" _) m _) args span => do
      let (fpath, sig) ← s.methodRef span m
      if sig.void then mismatch span s!"'{m}' changes the state: call it as a statement"
      let some (i, _) := s.lookup "this" | mismatch span "'this' outside a method"
      let ps := sig.params.drop 1
      if args.length != ps.length then mismatch span s!"'{m}' takes {ps.length} arguments"
      let given ← (args.zip ps).mapM fun (a, (_, τ)) => checkExpr T s a (some τ)
      let typedArgs := given.foldr (fun a acc => s!"(.cons {a.typed} {acc})") ".nil"
      let readableArgs := ident "this" :: given.map (·.term)
      let (argsT, argsS) := foldSafe given
      return { ty := sig.result, typed := s!"(.callThis {fpath} {s.varPath i} {typedArgs})",
               readable := " ".intercalate (ident m :: readableArgs), trivial := argsT && sig.trivial,
               safe := andTText argsT argsS sig.trivial (" ".intercalate (s!"{ident m}.safe" :: readableArgs)) }
    | .newMap .string _ span =>
      match expected with
      | some τ@(.map σ) => return { ty := τ, typed := s!"(.newMap {T.print σ})",
                                     readable := s!"([] : {T.lean τ})", atomic := true }
      | _ => mismatch span "new Map() needs a known type here"
    | .call (.var f _) args span => do
      let some j := s.fns.findIdx? (fun g => g.name == f && !g.method)
        | throw { code := "A2001", message := s!"'{f}' is not a function declared earlier", span }
      if s.locals.any (·.1 == f) then mismatch span s!"'{f}' is shadowed by a local"
      let sig := s.fns[j]!
      if args.length > sig.params.length then mismatch span s!"'{f}' takes {sig.params.length} arguments"
      let given ← (args.zip sig.params).mapM fun (a, (_, τ)) => checkExpr T s a (some τ)
      let omitted := sig.params.drop args.length
      if !omitted.all (fun (_, τ) => τ matches .option .undef _ | .option .both _) then
        mismatch span s!"'{f}' needs {sig.params.length} arguments"
      let typedArgs := given.foldr (fun a acc => s!"(.cons {a.typed} {acc})")
        (if omitted.isEmpty then ".nil" else "(.omitted (by decide +kernel))")
      let readableArgs := given.map (·.term) ++ omitted.map fun _ => "none"
      let readable := if readableArgs.isEmpty then ident f else " ".intercalate (ident f :: readableArgs)
      let (argsT, argsS) := foldSafe given
      let calleeSafe := " ".intercalate (s!"{ident f}.safe" :: readableArgs)
      return { ty := sig.result, typed := s!"(.call (s := sig.{ident f}) {fnPath (s.fns.length - 1 - j)} (by decide +kernel) {typedArgs})",
               readable, atomic := readableArgs.isEmpty, trivial := argsT && sig.trivial,
               safe := andTText argsT argsS sig.trivial calleeSafe }
    | .call (.member recv m _) args span => checkMethod T s recv m args span expected
    | .member a f span => do
      let a ← inferExpr T s a none
      match a.ty, f with
      | .array _, "length" | .string, "length" =>
        return { ty := .number, typed := s!"(.{if a.ty == .string then "slength" else "length"} {a.typed})",
                 readable := s!"(List.length {a.term} : Int)", atomic := true, trivial := a.trivial, safe := a.safe }
      | .record fs, _ =>
        let fields := Fields.toList fs
        match fields.findIdx? (·.1 == f) with
        | some k =>
          if protoName f then mismatch span s!"'{f}' is an Object.prototype property"
          let readable := match a.payload with
            | some p => T.payloadField a.ty p k
            | none => T.fieldText a.ty a.term k
          return { ty := fields[k]!.2, typed := s!"(.field {a.typed} {fidxPath k} (by decide +kernel))",
                   readable, atomic := true, trivial := a.trivial, safe := a.safe }
        | none => mismatch span s!"no field '{f}'"
      | τ, _ => mismatch span s!"field '{f}' of {τ.ts}"
    | .index a i span => do
      let a ← inferExpr T s a none
      let .array τ := a.ty | mismatch span s!"indexing {a.ty.ts}"
      if τ matches .option .. then mismatch span "indexing an array of optionals (a nested optional)"
      let i ← checkExpr T s i (some .number)
      return { ty := .option .undef τ, typed := s!"(.index {a.typed} {i.typed})",
               readable := s!"Ariadne.listIndex {a.term} {i.term}", trivial := a.trivial && i.trivial, safe := both a i }
    | .array elems span => do
      let τ ← match expected with
        | some (.array τ) => pure τ
        | _ => match elems with
          | .spread (.call (.member (.member (.var "this" _) _ _) "keys" _) [] _) _ :: _ => pure .string
          | .spread (.call (.member (.member (.var "this" _) f _) "values" _) [] _) _ :: _ => do
            pure (← s.stateField span f).2.2.2
          | .spread x _ :: _ => do
            let o ← inferExpr T s x none
            let .array τ := o.ty | mismatch span s!"spreading {o.ty.ts}"
            pure τ
          | x :: _ => pure (← inferExpr T s x none).ty
          | [] => mismatch span "an empty array literal needs a known type here"
      -- Each element: its constructor (with what precedes the rest), and its check.
      let outs ← elems.mapM fun
        | .spread (.call (.member (.member (.var "this" _) f _) "keys" _) [] _) sp => do
          let (path, fsT, j, _) ← s.stateField sp f
          if τ != .string then mismatch sp "map keys (strings) where another element type is expected"
          return (true, ({ ty := .array τ, typed := "", readable := s!"List.map Prod.fst {T.fieldText (.record fsT) (ident "this") j}" } : Out),
            s!"spreadKeys {path} {fidxPath j}")
        | .spread (.call (.member (.member (.var "this" _) f _) "values" _) [] _) sp => do
          let (path, fsT, j, σ) ← s.stateField sp f
          if τ != σ then mismatch sp s!"map values ({σ.ts}) where {τ.ts} is expected"
          return (true, ({ ty := .array τ, typed := "", readable := s!"List.map Prod.snd {T.fieldText (.record fsT) (ident "this") j}" } : Out),
            s!"spreadValues {path} {fidxPath j}")
        | .spread x _ => do
          let o ← checkExpr T s x (some (.array τ))
          return (true, o, s!"spread {o.typed}")
        | x => do
          let o ← checkExpr T s x (some τ)
          return (false, o, s!"cons {o.typed}")
      let typed := outs.foldr (fun (_, _, c) acc => s!"(.{c} {acc})") ".nil"
      let outs := outs.map fun (sp, o, _) => (sp, o)
      let readable := elemsText (outs.map fun (sp, o) => (sp, o.term))
      let (t, safe) := foldSafe (outs.map (·.2))
      return { ty := .array τ, typed := s!"(.array (τ := {T.print τ}) {typed})", readable, trivial := t, safe }
    | .record entries span => do
      match expected, entries with
      | some τ, _ => checkRecord T s entries span τ
      | none, ("", r) :: _ => do
        -- `{ ...r, … }` has the type of `r`.
        let o ← inferExpr T s r none
        checkRecord T s entries span o.ty
      | none, _ => mismatch span "an object literal needs a known type here"
    | e => unsupportedTy e.span "this expression"

  /-- The branches of `c ? a : b` at one type: the expected one, else the type of the
  branch that is not a nullish literal (made optional for the other). -/
  partial def checkBranches (T : Types) (sa : Scope) (a : Parse.Expr) (sb : Scope) (b : Parse.Expr)
      (expected : Option Ty) : Checked (Out × Out) := do
    if let some τ := expected then return (← checkExpr T sa a (some τ), ← checkExpr T sb b (some τ))
    let nullish : Parse.Expr → Option Nullish
      | .literal .undefined _ => some .undef
      | .literal .null _ => some .null
      | _ => none
    match nullish a with
    | some n => do
      let b ← inferExpr T sb b none
      let τ := match b.ty with
        | .option m σ => .option (if m == n then m else .both) σ
        | σ => .option n σ
      return (← checkExpr T sa a (some τ), ← coerce T {} b τ)
    | none => do
      let a ← inferExpr T sa a none
      let τ := match nullish b, a.ty with
        | some n, .option m σ => .option (if m == n then m else .both) σ
        | some n, σ => .option n σ
        | none, σ => σ
      return (← coerce T {} a τ, ← checkExpr T sb b (some τ))

  /-- An array method with a callback, or `includes`. -/
  partial def checkMethod (T : Types) (s : Scope) (recv : Parse.Expr) (m : String) (args : List Parse.Expr)
      (span : Span) (expected : Option Ty) : Checked Out := do
    let a ← inferExpr T s recv none
    let .array τ := a.ty | unsupportedTy span s!"the method '{m}' of {a.ty.ts}"
    let [arg] := args | unsupportedTy span s!"'{m}' with other than one argument"
    match m with
    | "includes" =>
      if !τ.prim then mismatch span s!"'includes' on an array of {τ.ts} (objects compare by identity)"
      let x ← checkExpr T s arg (some τ)
      return { ty := .bool, typed := s!"(.includes (by decide +kernel) {a.typed} {x.typed})",
               readable := s!"List.any {a.term} (fun y' => y' == {x.term})", trivial := a.trivial && x.trivial,
               safe := both a x }
    | "some" | "every" | "find" | "filter" | "map" => do
      let result := if m == "map" then (match expected with | some (.array σ) => some σ | _ => none) else some .bool
      let f ← checkFn T s span arg τ result
      let (ctor, ty, readable, cond) := match m with
        | "some" => ("any", Ty.bool, s!"List.any {a.term} {f.lam}", s!"Ariadne.anySafe {f.lam} {f.lamSafe} {a.term}")
        | "every" => ("all", .bool, s!"List.all {a.term} {f.lam}", s!"Ariadne.allSafe {f.lam} {f.lamSafe} {a.term}")
        | "find" => ("find", .option .undef τ, s!"List.find? {f.lam} {a.term}",
          s!"Ariadne.anySafe {f.lam} {f.lamSafe} {a.term}")
        | "filter" => ("filter", .array τ, s!"List.filter {f.lam} {a.term}", s!"List.all {a.term} {f.lamSafe}")
        | _ => ("map", .array f.ty, s!"List.map {f.lam} {a.term}", s!"List.all {a.term} {f.lamSafe}")
      if m == "find" && τ matches .option .. then mismatch span "'find' on an array of optionals (a nested optional)"
      return { ty, typed := s!"(.{ctor} {a.typed} {f.typed})", readable,
               trivial := a.trivial && f.trivial, safe := andTText a.trivial a.safe f.trivial cond }
    | "toSorted" => do
      let c ← checkCmp T s span arg τ
      let cond := if c.trivial then s!"Ariadne.consistent (Ariadne.signs {c.lam} {a.term})"
        else s!"Ariadne.sortSafe {c.lam} false {c.lamSafe} {a.term}"
      return { ty := .array τ, typed := s!"(.sorted {a.typed} {c.typed})",
               readable := s!"Ariadne.sortedBy {c.lam} {a.term}", trivial := false, safe := andText a.ok cond }
    | _ => unsupportedTy span s!"the array method '{m}'"

  /-- A callback on elements of type `τ`: `(x) => e`, `() => e`, or a declared function of
  one parameter. -/
  partial def checkFn (T : Types) (s : Scope) (span : Span) (arg : Parse.Expr) (τ : Ty) (result : Option Ty) :
      Checked Fn := do
    match arg with
    | .lambda [p] (.return_ body _) _ => do
      let f ← checkExpr T (← declare s span p.name τ) body result
      return { typed := s!"(.arrow {leanString p.name} {f.typed})", lam := s!"(fun {ident p.name} => {f.readable})",
               lamSafe := s!"(fun {ident p.name} => {f.safe})", trivial := f.trivial, ty := f.ty }
    | .lambda [] (.return_ body _) _ => do
      let f ← checkExpr T s body result
      return { typed := s!"(.const {f.typed})", lam := s!"(fun _ => {f.readable})",
               lamSafe := s!"(fun _ => {f.safe})", trivial := f.trivial, ty := f.ty }
    | .var f _ => do
      let (path, sig) ← s.fnRef span f
      let [(_, τ')] := sig.params | mismatch span s!"'{f}' as a callback must take one parameter"
      if τ' != τ then mismatch span s!"'{f}' takes {τ'.ts} where {τ.ts} is passed"
      if let some r := result then
        if r != sig.result then mismatch span s!"'{f}' returns {sig.result.ts} where {r.ts} is expected"
      return { typed := s!"(.ref {path} (by decide +kernel))", lam := ident f, lamSafe := s!"{ident f}.safe",
               trivial := sig.trivial, ty := sig.result }
    | .lambda .. => unsupportedTy span "a callback other than an arrow function with an expression body and at most one parameter"
    | _ => unsupportedTy span "a callback other than an arrow function or a declared function"

  /-- A comparator: `(x, y) => e`, or a declared function of two parameters. -/
  partial def checkCmp (T : Types) (s : Scope) (span : Span) (arg : Parse.Expr) (τ : Ty) : Checked Fn := do
    match arg with
    | .lambda [p, q] (.return_ body _) _ => do
      let (x, y) := (p.name, q.name)
      if x == y then mismatch span "a comparator with two parameters of the same name"
      let c ← checkExpr T (← declare (← declare s span y τ) span x τ) body (some .number)
      return { typed := s!"(.arrow {leanString x} {leanString y} {c.typed})",
               lam := s!"(fun {ident x} {ident y} => {c.readable})",
               lamSafe := s!"(fun {ident x} {ident y} => {c.safe})", trivial := c.trivial, ty := .number }
    | .var f _ => do
      let (path, sig) ← s.fnRef span f
      let [(_, τ1), (_, τ2)] := sig.params | mismatch span s!"'{f}' as a comparator must take two parameters"
      if τ1 != τ || τ2 != τ || sig.result != .number then
        mismatch span s!"'{f}' is not a comparator of {τ.ts}"
      return { typed := s!"(.ref {path} (by decide +kernel))", lam := ident f, lamSafe := s!"{ident f}.safe",
               trivial := sig.trivial, ty := .number }
    | _ => unsupportedTy span "a comparator other than an arrow function of two parameters or a declared function"

  partial def checkBinary (T : Types) (s : Scope) (op : String) (a b : Parse.Expr) (span : Span)
      (_expected : Option Ty) : Checked Out := do
    match op with
    | "&&" | "||" => do
      let a ← checkExpr T s a (some .bool)
      let b ← checkExpr T s b (some .bool)
      let cond := if op == "&&" then s!"if {a.term} then {paren b.safe} else true"
        else s!"if {a.term} then true else {paren b.safe}"
      return { ty := .bool, typed := s!"(.{if op == "&&" then "and" else "or"} {a.typed} {b.typed})",
               readable := s!"{a.term} {op} {b.term}", trivial := a.trivial && b.trivial,
               safe := andTText a.trivial a.safe b.trivial cond }
    | "==" | "!=" => do
      let .literal .null _ := b | unsupportedTy span s!"'{op}' other than against null"
      let a ← inferExpr T s a none
      let .option _ σ := a.ty | mismatch span s!"'{op} null' on {a.ty.ts}"
      if !σ.nonNullish then mismatch span "a nested optional"
      let (ctor, readable) := if op == "==" then ("isNull", s!"{a.term}.isNone") else ("notNull", s!"{a.term}.isSome")
      return { ty := .bool, typed := s!"(.{ctor} (by decide +kernel) {a.typed})", readable, trivial := a.trivial,
               safe := a.safe }
    | "??" => do
      let a ← inferExpr T s a none
      let .option _ σ := a.ty | mismatch span s!"'??' on {a.ty.ts}"
      if !σ.nonNullish then mismatch span "a nested optional"
      let b ← checkExpr T s b (some σ)
      return { ty := σ, typed := s!"(.coalesce (by decide +kernel) {a.typed} {b.typed})",
               readable := s!"match {a.readable} with | some v' => v' | none => {b.readable}",
               trivial := a.trivial && b.trivial,
               safe := andTText a.trivial a.safe b.trivial
                 s!"match {a.readable} with | some _ => true | none => {paren b.safe}" }
    | "===" | "!==" => do
      -- Type a literal operand against the other side.
      let (a, b) ← match a with
        | .literal .. => do let b ← inferExpr T s b none; pure (← checkExpr T s a (some b.ty), b)
        | _ => do let a ← inferExpr T s a none; pure (a, ← checkExpr T s b (some a.ty))
      if !a.ty.prim then mismatch span s!"'{op}' on {a.ty.ts} (objects compare by identity)"
      let neg := op == "!=="
      return { ty := .bool, typed := s!"(.bin (.{if neg then "ne" else "eq"} (by decide +kernel)) {a.typed} {b.typed})",
               readable := s!"{a.term} {if neg then "!=" else "=="} {b.term}", trivial := a.trivial && b.trivial,
               safe := both a b }
    | _ => do
      let a ← inferExpr T s a none
      let b ← checkExpr T s b (some a.ty)
      let mk (ty : Ty) (ctor readable : String) : Out :=
        { ty, typed := s!"(.bin .{ctor} {a.typed} {b.typed})", readable, trivial := a.trivial && b.trivial,
          safe := both a b }
      -- Number arithmetic stays exact only within the safe-integer range.
      let arith (ctor sym : String) : Out :=
        { ty := .number, typed := s!"(.bin .{ctor} {a.typed} {b.typed})", readable := s!"{a.term} {sym} {b.term}",
          trivial := false, safe := andText (both a b) s!"Ariadne.inRange ({a.term} {sym} {b.term})" }
      match op, a.ty with
      | "+", .int => pure (mk .int "add" s!"{a.term} + {b.term}")
      | "-", .int => pure (mk .int "sub" s!"{a.term} - {b.term}")
      | "*", .int => pure (mk .int "mul" s!"{a.term} * {b.term}")
      | "+", .number => pure (arith "nadd" "+")
      | "-", .number => pure (arith "nsub" "-")
      | "*", .number => pure (arith "nmul" "*")
      | "+", .string => pure (mk .string "concat" s!"{a.term} ++ {b.term}")
      | "<", .int => pure (mk .bool "lt" s!"decide ({a.term} < {b.term})")
      | "<=", .int => pure (mk .bool "le" s!"decide ({a.term} ≤ {b.term})")
      | ">", .int => pure (mk .bool "gt" s!"decide ({a.term} > {b.term})")
      | ">=", .int => pure (mk .bool "ge" s!"decide ({a.term} ≥ {b.term})")
      | "<", .number => pure (mk .bool "nlt" s!"decide ({a.term} < {b.term})")
      | "<=", .number => pure (mk .bool "nle" s!"decide ({a.term} ≤ {b.term})")
      | ">", .number => pure (mk .bool "ngt" s!"decide ({a.term} > {b.term})")
      | ">=", .number => pure (mk .bool "nge" s!"decide ({a.term} ≥ {b.term})")
      | "<", .string => pure (mk .bool "slt" s!"Ariadne.strLt {a.term} {b.term}")
      | "<=", .string => pure (mk .bool "sle" s!"Ariadne.strLe {a.term} {b.term}")
      | ">", .string => pure (mk .bool "sgt" s!"Ariadne.strLt {b.term} {a.term}")
      | ">=", .string => pure (mk .bool "sge" s!"Ariadne.strLe {b.term} {a.term}")
      | op, τ => mismatch span s!"'{op}' does not apply to {τ.ts}"

  /-- An object literal at a record or union type. -/
  partial def checkRecord (T : Types) (s : Scope) (entries : List (String × Parse.Expr)) (span : Span) :
      Ty → Checked Out
    | .union key vs => do
      let some tagExpr := entries.lookup key | mismatch span s!"the literal has no '{key}' field"
      let variants := Variants.toList vs
      let tag? : Option TagLit := match tagExpr with
        | .literal (.string u) _ => some (.str u)
        | .literal (.boolean b) _ => some (.bool b)
        | _ => none
      let some tag := tag? | mismatch span s!"'{key}' must be a literal"
      let some i := variants.findIdx? (·.1 == tag) | mismatch span s!"no variant tagged {tagLitTS tag}"
      let (t, fs) := variants[i]!
      let r ← checkRecord T s entries span (vrec' key t fs)
      -- The variant's payload: its fields after the tag.
      let terms := r.fieldTerms.drop 1
      let payload : Payload := match terms with
        | [] => { kind := .unit, text := "()" }
        | [x] => { kind := .single, text := x }
        | _ =>
          let ctor := match T.payloadName? (.union key vs) i with
            | some V => if namesFree fs then some s!"{V}.mk" else none
            | none => none
          { kind := .multi, text := match ctor with
            | some c => s!"({" ".intercalate (c :: terms)})"
            | none => "(" ++ ", ".intercalate (terms ++ ["()"]) ++ ")" }
      coerce T span { r with readable := s!"((), {payload.whole})", atomic := true, payload := some payload }
        (.union key vs)
    | τ@(.record fs) => do
      let fields := Fields.toList fs
      match entries with
      | ("", r) :: rest => do
        -- `{ ...r, f: e, … }`
        let r ← checkExpr T s r (some τ)
        let src ← rest.mapM fun (f, e) => do
          if f.isEmpty then unsupportedTy span "a spread after the first entry"
          let some fτ := fields.lookup f | mismatch span s!"no field '{f}'"
          return (f, ← checkExpr T s e (some fτ))
        let srcNames := src.map (·.1)
        let typedEntries := src.foldr (fun (f, o) acc => s!"(.cons {leanString f} {o.typed} {acc})") ".nil"
        let (upd, readable) := fields.zipIdx.foldr (fun ((f, _), k) (accU, accR) =>
            match srcNames.findIdx? (· == f) with
            | some j => (s!"(.set {fidxPath j} {accU})", src[j]!.2.term :: accR)
            | none => (s!"(.keep (by decide +kernel) {accU})", projText "r'" k :: accR)) (".nil", [])
        let (esT, esS) := foldSafe (src.map (·.2))
        -- With setters, `{ ...r, f: v }` is `r.withF v`.
        let text := match T.recordName? τ with
          | some _ => src.foldl (fun acc (f, o) => match fields.findIdx? (·.1 == f) with
              | some k => s!"({T.setText τ acc k o.readable})"
              | none => acc) r.term
          | none => s!"let r' := {r.readable}; ({", ".intercalate (readable ++ ["()"])})"
        return { ty := τ, typed := s!"(.update {r.typed} {typedEntries} {upd} (by decide +kernel))",
                 readable := text, trivial := r.trivial && esT, safe := andTText r.trivial r.safe esT esS }
      | _ => do
        let src ← entries.mapM fun (f, e) => do
          if f.isEmpty then unsupportedTy span "a spread after the first entry"
          let some fτ := fields.lookup f | mismatch span s!"no field '{f}'"
          return (f, ← checkExpr T s e (some fτ))
        let srcNames := src.map (·.1)
        let typedEntries := src.foldr (fun (f, o) acc => s!"(.cons {leanString f} {o.typed} {acc})") ".nil"
        let sel ← fields.foldrM (fun (f, fτ) (accS, accR) =>
            match srcNames.findIdx? (· == f) with
            | some j => pure (s!"(.cons {fidxPath j} {accS})", src[j]!.2.term :: accR)
            | none => match fτ with
              | .option .undef _ | .option .both _ => pure (s!"(.absent (by decide +kernel) {accS})", "none" :: accR)
              | _ => mismatch span s!"the literal has no '{f}' field") (".nil", [])
        let (esT, esS) := foldSafe (src.map (·.2))
        let readable := match T.recordName? τ with
          | some n => if sel.2.isEmpty then s!"{ident n}.mk" else s!"({" ".intercalate (s!"{ident n}.mk" :: sel.2)})"
          | none => "(" ++ ", ".intercalate (sel.2 ++ ["()"]) ++ ")"
        return { ty := τ, typed := s!"(.record {typedEntries} {sel.1} (by decide +kernel))",
                 readable, atomic := true, trivial := esT, safe := esS, fieldTerms := sel.2 }
    | τ@(.option _ σ) => do
      let r ← checkRecord T s entries span σ
      coerce T span r τ
    | τ => mismatch span s!"an object literal where {τ.ts} is expected"
end

/-! ## Statements -/

/-- Readable continuations, rendered at the indentation where they are placed. -/
structure KText where
  normal : String → String
  brk : String → String
  cont : String → String

def KText.wrap (k : KText) (n : Narrowed) : KText := ⟨n.wrap k.normal, n.wrap k.brk, n.wrap k.cont⟩

/-- A checked statement list: typed syntax, readable printers of its denotation and
of its safety condition (each taking the continuations' text), and how it can end. -/
structure Block where
  typed : String
  readable : (indent : String) → KText → String
  safe : (indent : String) → KText → String
  trivial : Bool
  falls : Bool
  breaks : Bool
  continues : Bool

def blockNil : Block where
  typed := ".nil"
  readable i k := k.normal i
  safe i k := k.normal i
  trivial := true
  falls := true
  breaks := false
  continues := false

instance : Inhabited Block := ⟨blockNil⟩

/-- An `if` branch's statements. -/
def branchStmts : Parse.Stmt → List Parse.Stmt
  | .block ss _ => ss
  | s => [s]

/-- A checked `switch` case. -/
inductive SwitchArm where
  | empty (l : Option TagLit)
  | wide (l : Option TagLit) (b : Block)
  | narrow (j : Nat) (b : Block) (n : Narrowed)

instance : Inhabited SwitchArm := ⟨.empty none⟩

def SwitchArm.body? : SwitchArm → Option Block
  | .empty _ => none
  | .wide _ b | .narrow _ b _ => some b

/-- What a `switch` runs for one variant. -/
inductive Leaf where
  | narrowed (b : Block) (n : Narrowed)
  | run (b : Block)
  | normal

/-- A variable's value in an environment tuple: a narrowed variable is bound to its payload. -/
def Scope.valueText (s : Scope) (x : String) : String :=
  match s.payloads.lookup x with
  | some .unit => "((), ())"
  | some .single => s!"((), ({ident x}, ()))"
  | some .multi => s!"((), {ident x})"
  | none => ident x

/-- The environment tuple of a scope, as readable text. -/
def tupleText (s : Scope) : String :=
  "(" ++ ", ".intercalate (s.locals.map (s.valueText ·.1) ++ ["()"]) ++ ")"

/-- The pattern a continuation binds the environment tuple with: the scope's variables `text` uses, by
name (a narrowed variable to its payload), `_` for the others. -/
def statePattern (s : Scope) (text : String) : String :=
  let uses (x : String) := (text.splitOn (ident x)).length > 1
  if !s.locals.any (uses ·.1) then "_" else
  "(" ++ ", ".intercalate (s.locals.map (fun (x, _) => if !uses x then "_" else match s.payloads.lookup x with
    | some .unit => "_"
    | some .single => s!"((), ({ident x}, ()))"
    | some .multi => s!"((), {ident x})"
    | none => ident x) ++ ["()"]) ++ ")"

/-- Readable `switch`: a match on the union's constructors (or nested matches on its sum), one leaf per
variant; a narrowed variable is bound to its variant's payload. -/
def switchLeaves (render : Block → String → KText → String) (x : String) (ctors : Option (List String))
    (arities : List Nat) (leaves : List Leaf) (k : KText) (scrut ind : String) : String :=
  let leafText (l : Leaf) (j : String) : String := match l with
    | .narrowed b n => render b j (k.wrap n)
    | .run b => render b j k
    | .normal => k.normal j
  -- What a leaf's pattern binds: the narrowed variable's payload, else nothing.
  let bind (l : Leaf) (arity : Nat) (inSum : Bool) : String := match l, arity with
    | .narrowed .., 0 => "_"
    | .narrowed .., 1 => if inSum then s!"({ident x}, ())" else ident x
    | .narrowed .., _ => ident x
    | _, _ => "_"
  let j := ind ++ "  "
  match ctors, leaves with
  | _, [l] => leafText l ind
  | some cs, _ =>
    let arms := (cs.zip (arities.zip leaves)).map fun (c, (a, l)) =>
      s!"{ind}| {if a == 0 then c else s!"{c} {bind l a false}"} =>\n{j}{leafText l j}"
    s!"match {scrut} with\n" ++ "\n".intercalate arms
  | none, _ =>
    let rec nested (ls : List (Leaf × Nat)) (scrut ind : String) : String :=
      let j := ind ++ "  "
      match ls with
      | [] => ""
      | [(l, _)] => leafText l ind
      | (l, a) :: [(l', a')] =>
        s!"match {scrut} with\n{ind}| Sum.inl {bind l a true} =>\n{j}{leafText l j}\n" ++
          s!"{ind}| Sum.inr {bind l' a' true} =>\n{j}{leafText l' j}"
      | (l, a) :: more =>
        s!"match {scrut} with\n{ind}| Sum.inl {bind l a true} =>\n{j}{leafText l j}\n" ++
          s!"{ind}| Sum.inr p' =>\n{j}{nested more "p'" j}"
    nested (leaves.zip arities) scrut ind

/-- `if (c) yes else no; rest`, rendered for the denotation or the safety condition.
When both branches may complete, the rest is bound once as a join point instead of
being repeated in each branch. -/
def iteText (render : Block → String → KText → String) (s : Scope) (c : String)
    (yes no rest : Block) (i : String) (k : KText) : String :=
  let j := i ++ "  "
  if yes.falls && no.falls && rest.typed != ".nil" then
    let after := s!"after{i.length}'"
    let k' := { k with normal := fun _ => s!"{after} {tupleText s}" }
    let restText := render rest j k
    s!"let {after} := fun {statePattern s restText} =>\n{j}{restText}\n{i}" ++
      s!"if {c} then\n{j}{render yes j k'}\n{i}else\n{j}{render no j k'}"
  else
    let k' := { k with normal := fun j' => render rest j' k }
    s!"if {c} then\n{j}{render yes j k'}\n{i}else\n{j}{render no j k'}"

/-- A loop: `Ariadne.forIn items (fun binder next exit state => body) (fun state => rest) tuple`. -/
def loopText (render : Block → String → KText → String) (s : Scope) (items binder : String)
    (pre : String → String)
    (body rest : Block) (i : String) (k : KText) : String :=
  let d := i.length
  let (nx, ex) := (s!"next{d}'", s!"exit{d}'")
  let tup := tupleText s
  let j := i ++ "  "
  let kb : KText := ⟨fun _ => s!"{nx} {tup}", fun _ => s!"{ex} {tup}", fun _ => s!"{nx} {tup}"⟩
  let bodyText := s!"{pre j}{render body j kb}"
  let restText := render rest j k
  s!"Ariadne.forIn {items} (fun {binder} {nx} {ex} {statePattern s bodyText} =>\n{j}{bodyText})\n{i}  " ++
    s!"(fun {statePattern s restText} =>\n{j}{restText})\n{i}  {tup}"

def flagsIte (yes no rest : Block) : Bool × Bool × Bool :=
  ((yes.falls || no.falls) && rest.falls,
   yes.breaks || no.breaks || ((yes.falls || no.falls) && rest.breaks),
   yes.continues || no.continues || ((yes.falls || no.falls) && rest.continues))

mutual
  partial def checkStmts (T : Types) (s : Scope) (result : Ty) : List Parse.Stmt → Checked Block
    | [] => pure blockNil
    | .let_ false x annotation e span :: rest => do
      let expected ← annotation.mapM (T.resolve span 64)
      let v ← checkExpr T s e expected
      let rest ← checkStmts T (← declare s span x v.ty) result rest
      pure { typed := s!"(.const {leanString x} {v.typed}\n  {rest.typed})",
             readable := fun i k => s!"let {ident x} : {T.lean v.ty} := {v.readable}\n{i}{rest.readable i k}",
             safe := fun i k => andText v.ok s!"let {ident x} : {T.lean v.ty} := {v.readable}\n{i}{rest.safe i k}",
             trivial := v.trivial && rest.trivial,
             falls := rest.falls, breaks := rest.breaks, continues := rest.continues }
    | .let_ true x annotation e span :: rest => do
      let expected ← annotation.mapM (T.resolve span 64)
      let v ← checkExpr T s e expected
      let s' ← declare s span x v.ty
      let rest ← checkStmts T { s' with mutables := x :: s'.mutables } result rest
      pure { typed := s!"(.let_ {leanString x} {v.typed}\n  {rest.typed})",
             readable := fun i k => s!"let {ident x} : {T.lean v.ty} := {v.readable}\n{i}{rest.readable i k}",
             safe := fun i k => andText v.ok s!"let {ident x} : {T.lean v.ty} := {v.readable}\n{i}{rest.safe i k}",
             trivial := v.trivial && rest.trivial,
             falls := rest.falls, breaks := rest.breaks, continues := rest.continues }
    | .assign (.var x _) e span :: rest => do
      let some (j, τ) := s.lookup x | throw { code := "A2001", message := s!"unknown variable '{x}'", span }
      if !s.mutables.contains x then mismatch span s!"'{x}' is not assignable (a const declaration)"
      let v ← checkExpr T s e (some τ)
      let rest ← checkStmts T s result rest
      -- A narrowed variable stays bound to its payload.
      let bind := match s.payloads.lookup x with
        | some .unit => ""
        | some kind =>
          let p := v.payload.getD (match kind with
            | .single => { kind, text := s!"{v.term}.2.1" }
            | _ => { kind, text := s!"{v.term}.2" })
          s!"let {ident x} := {p.text}"
        | none => s!"let {ident x} : {T.lean v.ty} := {v.readable}"
      let bindIn (i body : String) := if bind.isEmpty then body else s!"{bind}\n{i}{body}"
      pure { typed := s!"(.assign {s.varPath j} {v.typed}\n  {rest.typed})",
             readable := fun i k => bindIn i (rest.readable i k),
             safe := fun i k => andText v.ok (bindIn i (rest.safe i k)),
             trivial := v.trivial && rest.trivial,
             falls := rest.falls, breaks := rest.breaks, continues := rest.continues }
    | .continue_ _ :: rest => do
      let rest ← checkStmts T s result rest
      pure { typed := s!"(.cont {rest.typed})", readable := (fun i k => k.cont i), safe := (fun i k => k.cont i),
             trivial := rest.trivial, falls := false, breaks := false, continues := true }
    | .forOf false x e body span :: rest => do
      let body := branchStmts body
      let a ← inferExpr T s e none
      let .array σ := a.ty | mismatch span s!"for-of over {a.ty.ts}"
      let body ← checkStmts T (← declare s span x σ) result body
      let rest ← checkStmts T s result rest
      let text (render : Block → String → KText → String) :=
        loopText render s a.term (ident x) (fun _ => "") body rest
      pure { typed := s!"(.forOf {leanString x} {a.typed}\n  {body.typed}\n  {rest.typed})",
             readable := text (·.readable), safe := fun i k => andText a.ok (text (·.safe) i k),
             trivial := a.trivial && body.trivial && rest.trivial,
             falls := rest.falls, breaks := rest.breaks, continues := rest.continues }
    | .for_ (.let_ true i _ (.literal (.number 0 0) _) _) (.binary "<" (.var i₁ _) (.var n _) _)
        (.assign (.var i₂ _) (.binary "+" (.var i₃ _) (.literal (.number 1 0) _) _) _) body span :: rest => do
      if !(i₁ == i && i₂ == i && i₃ == i) then unsupportedTy span "this for loop"
      let some (j, τ) := s.lookup n | throw { code := "A2001", message := s!"unknown variable '{n}'", span }
      if τ != .number then mismatch span s!"the bound '{n}' is {τ.ts}, not a number"
      if s.mutables.contains n then mismatch span s!"the bound '{n}' must be a const"
      -- The index is not assignable in the body (it is not added to the mutables).
      let body ← checkStmts T (← declare s span i .number) result (branchStmts body)
      let rest ← checkStmts T s result rest
      let text (render : Block → String → KText → String) :=
        loopText render s s!"(Ariadne.range {ident n})" (ident i) (fun _ => "") body rest
      pure { typed := s!"(.forRange {leanString i} {s.varPath j}\n  {body.typed}\n  {rest.typed})",
             readable := text (·.readable), safe := text (·.safe), trivial := body.trivial && rest.trivial,
             falls := rest.falls, breaks := rest.breaks, continues := rest.continues }
    | .forOfPair false ix x (.call (.member e "entries" _) [] _) (.block body _) span :: rest => do
      let a ← inferExpr T s e none
      let .array σ := a.ty | mismatch span s!"entries of {a.ty.ts}"
      if ix == x then mismatch span "an index and an element of the same name"
      let body ← checkStmts T (← declare (← declare s span ix .number) span x σ) result body
      let rest ← checkStmts T s result rest
      let p := s!"n{s.locals.length}'"
      let text (render : Block → String → KText → String) :=
        loopText render s s!"(List.zipIdx {a.term})" s!"({ident x}, {p})"
          (fun j => s!"let {ident ix} := ({p} : Int)\n{j}") body rest
      pure { typed := s!"(.forEntries {leanString ix} {leanString x} {a.typed}\n  {body.typed}\n  {rest.typed})",
             readable := text (·.readable), safe := fun i k => andText a.ok (text (·.safe) i k),
             trivial := a.trivial && body.trivial && rest.trivial,
             falls := rest.falls, breaks := rest.breaks, continues := rest.continues }
    | .return_ e span :: rest => do
      if s.void then
        let .literal .undefined _ := e | mismatch span "a value returned from a method returning void"
        let some (ti, _) := s.lookup "this" | mismatch span "'this' outside a method"
        let rest ← checkStmts T s result rest
        return { typed := s!"(.retVoid {s.varPath ti} {rest.typed})", readable := fun _ _ => ident "this",
                 safe := fun _ _ => "true", trivial := rest.trivial, falls := false, breaks := false, continues := false }
      let v ← checkExpr T s e (some result)
      let rest ← checkStmts T s result rest
      pure { typed := s!"(.ret {v.typed} {rest.typed})", readable := fun _ _ => v.readable, safe := fun _ _ => v.ok,
             trivial := v.trivial && rest.trivial, falls := false, breaks := false, continues := false }
    | .expr (.call (.member (.member (.var "this" _) f _) op _) args _) span :: rest => do
      if !s.void then mismatch span "only a method returning void may change the state"
      let (path, fs, j, τ) ← s.stateField span f
      let some (_, σ) := s.lookup "this" | mismatch span "'this' outside a method"
      let n := (Fields.toList fs).length
      let field := T.fieldText (.record fs) (ident "this") j
      let (typedOp, newMap, key, others) ← match op, args with
        | "set", [k, v] => do
          let key ← checkExpr T s k (some .string)
          let v ← checkExpr T s v (some τ)
          pure (s!"(.stateSet {path} {fidxPath j} (by decide +kernel) {key.typed} {v.typed}",
            s!"Ariadne.mapPut {field} {key.term} {v.term}", key, [v])
        | "delete", [k] => do
          let key ← checkExpr T s k (some .string)
          pure (s!"(.stateDelete {path} {fidxPath j} (by decide +kernel) {key.typed}", s!"Ariadne.mapDel {field} {key.term}", key, [])
        | _, _ => unsupportedTy span s!"this.{f}.{op}(…) as a statement"
      let rest ← checkStmts T s result rest
      let _ := n
      let upd := s!"let {ident "this"} : {T.lean σ} := {T.setText (.record fs) (ident "this") j newMap}"
      let operands := match others with
        | [v] => both key v
        | _ => key.ok
      pure { typed := s!"{typedOp}\n  {rest.typed})",
             readable := fun i k => s!"{upd}\n{i}{rest.readable i k}",
             safe := fun i k => andText operands s!"{upd}\n{i}{rest.safe i k}",
             trivial := key.trivial && others.all (·.trivial) && rest.trivial,
             falls := rest.falls, breaks := rest.breaks, continues := rest.continues }
    | .expr (.call (.member (.var "this" _) m _) args _) span :: rest => do
      if !s.void then mismatch span "only a method returning void may change the state"
      let (fpath, sig) ← s.methodRef span m
      if !sig.void then mismatch span s!"'{m}' returns a value: use its result"
      let some (ti, σ) := s.lookup "this" | mismatch span "'this' outside a method"
      let ps := sig.params.drop 1
      if args.length != ps.length then mismatch span s!"'{m}' takes {ps.length} arguments"
      let given ← (args.zip ps).mapM fun (a, (_, τ)) => checkExpr T s a (some τ)
      let typedArgs := given.foldr (fun a acc => s!"(.cons {a.typed} {acc})") ".nil"
      let readableArgs := ident "this" :: given.map (·.term)
      let (argsT, argsS) := foldSafe given
      let rest ← checkStmts T s result rest
      let upd := s!"let {ident "this"} : {T.lean σ} := {" ".intercalate (ident m :: readableArgs)}"
      let callSafe := andTText argsT argsS sig.trivial (" ".intercalate (s!"{ident m}.safe" :: readableArgs))
      pure { typed := s!"(.callVoid {fpath} {s.varPath ti} {typedArgs}\n  {rest.typed})",
             readable := fun i k => s!"{upd}\n{i}{rest.readable i k}",
             safe := fun i k => andText callSafe s!"{upd}\n{i}{rest.safe i k}",
             trivial := argsT && sig.trivial && rest.trivial,
             falls := rest.falls, breaks := rest.breaks, continues := rest.continues }
    | .break_ _ :: rest => do
      let rest ← checkStmts T s result rest
      pure { typed := s!"(.brk {rest.typed})", readable := (fun i k => k.brk i), safe := (fun i k => k.brk i),
             trivial := rest.trivial, falls := false, breaks := true, continues := false }
    | .block body _ :: rest => do
      let body ← checkStmts T s result body
      let rest ← checkStmts T s result rest
      pure { typed := s!"(.block {body.typed}\n  {rest.typed})",
             readable := fun i k => body.readable i { k with normal := fun j => rest.readable j k },
             safe := fun i k => body.safe i { k with normal := fun j => rest.safe j k },
             trivial := body.trivial && rest.trivial,
             falls := body.falls && rest.falls, breaks := body.breaks || (body.falls && rest.breaks),
             continues := body.continues || (body.falls && rest.continues) }
    | .if_ c yes no span :: rest =>
      match nullTestVar c with
      | some (x, isNull) => checkNullIf T s result x isNull (branchStmts yes) (branchStmts no) span rest
      | none => do
        let c ← checkExpr T s c (some .bool)
        let yes ← checkStmts T s result (branchStmts yes)
        let no ← checkStmts T s result (branchStmts no)
        let rest ← checkStmts T s result rest
        let (falls, breaks, continues) := flagsIte yes no rest
        pure { typed := s!"(.ite {c.typed}\n  {yes.typed}\n  {no.typed}\n  {rest.typed})",
               readable := iteText (·.readable) s c.readable yes no rest,
               safe := fun i k => andText c.ok (iteText (·.safe) s c.readable yes no rest i k),
               trivial := c.trivial && yes.trivial && no.trivial && rest.trivial, falls, breaks, continues }
    | .switch_ e cases span :: rest => checkSwitch T s result e cases span rest
    | st :: _ => unsupportedTy st.span "this statement"

  partial def checkNullIf (T : Types) (s : Scope) (result : Ty) (x : String) (isNull : Bool)
      (yesSs noSs : List Parse.Stmt) (span : Span) (rest : List Parse.Stmt) : Checked Block := do
    let (n, path) ← s.nullNarrowing span x
    let narrowed := s.narrow n.index n.narrow
    if isNull then
      let yes ← checkStmts T s result yesSs
      if noSs.isEmpty && !yes.falls then
        -- `if (x == null) exit; rest` with `x` narrowed in the rest.
        let rest ← checkStmts T narrowed result rest
        let text (render : Block → String → KText → String) (i : String) (k : KText) :=
          let j := i ++ "  "
          s!"match {ident x} with\n{i}| none =>\n{j}{render yes j k}\n{i}| some {ident x} =>\n{j}{render rest j (k.wrap n)}"
        return { typed := s!"(.ifNullExit {path} (by decide +kernel)\n  {yes.typed}\n  {rest.typed})",
                 readable := text (·.readable), safe := text (·.safe), trivial := yes.trivial && rest.trivial,
                 falls := rest.falls, breaks := yes.breaks || rest.breaks,
                 continues := yes.continues || rest.continues }
      let no ← checkStmts T narrowed result noSs
      let rest ← checkStmts T s result rest
      let text (render : Block → String → KText → String) (i : String) (k : KText) :=
        let j := i ++ "  "
        let k' := { k with normal := fun j' => render rest j' k }
        s!"match {ident x} with\n{i}| none =>\n{j}{render yes j k'}\n{i}| some {ident x} =>\n{j}{render no j (k'.wrap n)}"
      let (falls, breaks, continues) := flagsIte yes no rest
      return { typed := s!"(.ifNull {path} (by decide +kernel)\n  {yes.typed}\n  {no.typed}\n  {rest.typed})",
               readable := text (·.readable), safe := text (·.safe),
               trivial := yes.trivial && no.trivial && rest.trivial, falls, breaks, continues }
    else
      let yes ← checkStmts T narrowed result yesSs
      let no ← checkStmts T s result noSs
      let rest ← checkStmts T s result rest
      let text (render : Block → String → KText → String) (i : String) (k : KText) :=
        let j := i ++ "  "
        let k' := { k with normal := fun j' => render rest j' k }
        s!"match {ident x} with\n{i}| some {ident x} =>\n{j}{render yes j (k'.wrap n)}\n{i}| none =>\n{j}{render no j k'}"
      let (falls, breaks, continues) := flagsIte yes no rest
      return { typed := s!"(.ifNotNull {path} (by decide +kernel)\n  {yes.typed}\n  {no.typed}\n  {rest.typed})",
               readable := text (·.readable), safe := text (·.safe),
               trivial := yes.trivial && no.trivial && rest.trivial, falls, breaks, continues }

  /-- `switch (x.key)` over a union-typed local: cases in any order, grouped labels and
  `default`. A case with one label (not reached by falling through) narrows `x`. -/
  partial def checkSwitch (T : Types) (s : Scope) (result : Ty) (e : Parse.Expr)
      (cases : List (Option Parse.Expr × List Parse.Stmt)) (span : Span) (rest : List Parse.Stmt) : Checked Block := do
    let .member (.var x _) key _ := e | unsupportedTy span "a switch other than on a union's tag field"
    let some (i, τ@(.union key' vs)) := s.lookup x | mismatch span s!"'{x}' is not a union"
    if key != key' then mismatch span s!"'{key}' is not the tag field of '{x}'"
    if protoName key then mismatch span s!"'{key}' is an Object.prototype property"
    let variants := Variants.toList vs
    let n := variants.length
    let labels ← cases.mapM fun (l, _) => match l with
      | none => pure none
      | some (.literal (.string u) _) => pure (some (TagLit.str u))
      | some (.literal (.boolean b) _) => pure (some (TagLit.bool b))
      | some _ => unsupportedTy span "a case label other than a string or boolean literal"
    for l in labels do
      if let some t := l then
        if !variants.any (·.1 == t) then mismatch span s!"no variant tagged {tagLitTS t}"
    let tags := labels.filterMap id
    if tags.length != tags.eraseDups.length then mismatch span "a case label repeated"
    if (labels.filter (·.isNone)).length > 1 then mismatch span "more than one default"
    let arms ← (cases.zip labels).zipIdx.mapM fun (((_, body), l), p) => do
      let reached := p > 0 && ((cases[p - 1]?.map (·.2.isEmpty)).getD false)
      if body.isEmpty then return SwitchArm.empty l
      match l with
      | some t =>
        if !reached then
          let j := (variants.findIdx? (·.1 == t)).get!
          let (t, fs) := variants[j]!
          let σ := vrec' key t fs
          -- In the case, `x` is bound to the variant's payload (a one-variant union's value is its payload).
          let kind : PKind := if n == 1 then .multi else match Fields.toList fs with
            | [] => .unit
            | [_] => .single
            | _ => .multi
          let payload : Payload := { kind, text := if kind == .unit then "()" else ident x }
          let embed := if n == 1 then ident x else s!"({T.injectText τ j payload} : {T.lean τ})"
          let nar : Narrowed := { index := i, name := x, wide := τ, narrow := σ, embed }
          let s' := { s.narrow i σ with payloads := (x, kind) :: s.payloads }
          return SwitchArm.narrow j (← checkStmts T s' result body) nar
        return SwitchArm.wide l (← checkStmts T s result body)
      | none => return SwitchArm.wide l (← checkStmts T s result body)
    for (arm, p) in arms.zipIdx do
      if p + 1 < arms.length && (arm.body?.map (·.falls)).getD false then
        unsupportedTy span s!"case {p + 1} falls through to the next case"
    let rest ← checkStmts T s result rest
    let printLabel : Option TagLit → String
      | none => "none"
      | some t => s!"(some {printTag t})"
    let armsTyped := arms.foldr (fun arm acc => match arm with
      | .empty l => s!"(.empty {printLabel l} {acc})"
      | .wide l b => s!"(.wide {printLabel l} {b.typed}\n  {acc})"
      | .narrow j b _ => s!"(.narrow {vidxPath j n} {b.typed}\n  {acc})") ".nil"
    -- What each variant runs: its case, else the last default, else nothing.
    let firstFrom (p : Nat) : Leaf :=
      match (arms.drop p).find? (fun a => !(a matches .empty _)) with
      | some (.wide _ b) => .run b
      | _ => .normal
    let leaves := variants.map fun (t, _) =>
      match labels.findIdx? (· == some t) with
      | some p => match arms[p]? with
        | some (SwitchArm.narrow _ b nar) => Leaf.narrowed b nar
        | _ => firstFrom p
      | none => match (labels.zipIdx.filter (·.1.isNone)).getLast? with
        | some (_, q) => firstFrom q
        | none => .normal
    let bodies := arms.filterMap (·.body?)
    let armsFalls := bodies.any (·.falls) || (arms.getLast?.map (· matches .empty _)).getD false
    let covers := labels.contains none || variants.all fun (t, _) => labels.contains (some t)
    let f := armsFalls || bodies.any (·.breaks) || !covers
    let arities := variants.map fun (_, fs) => (Fields.toList fs).length
    let text (render : Block → String → KText → String) (ind : String) (k : KText) :=
      let kr := fun j => render rest j k
      switchLeaves render x (T.ctorNames? τ) arities leaves { k with normal := kr, brk := kr } (ident x) ind
    pure { typed := s!"(.switchG {s.varPath i} (by decide +kernel)\n  {armsTyped}\n  {rest.typed})",
           readable := text (·.readable), safe := text (·.safe),
           trivial := bodies.all (·.trivial) && rest.trivial,
           falls := f && rest.falls, breaks := f && rest.breaks,
           continues := bodies.any (·.continues) || (f && rest.continues) }
end

/-! ## Functions and files -/

structure CheckedFn where
  sig : FnSig
  body : Block

/-- A function, or a method of a class whose state has type `this` (a method
returning `void` changes the state and denotes the state it leaves). -/
def checkFunction (T : Types) (fns : List FnSig) (f : Parse.Function) (this : Option Ty := none) :
    Checked CheckedFn := do
  if fns.any (·.name == f.name) then
    throw { code := "A2004", message := s!"'{f.name}' is declared twice", span := f.span }
  let void := this.isSome && f.result matches .void
  let result ← match this, void with
    | some σ, true => pure σ
    | _, _ => T.resolve f.span 64 f.result
  let mut s : Scope := { fns, locals := (this.map fun σ => [("this", σ)]).getD [], void }
  let mut params := (this.map fun σ => [("this", σ)]).getD []
  for p in f.params do
    let τ ← T.param p
    params := params ++ [(p.name, τ)]
    if s.locals.any (·.1 == p.name) || fns.any (fun g => g.name == p.name && !g.method) ||
        (this.isNone && p.name == f.name) then
      throw { code := "A2004", message := s!"'{p.name}' shadows a declaration in scope", span := p.span }
    s := { s with locals := s.locals ++ [(p.name, τ)], mutables := p.name :: s.mutables }
  let .block body _ := f.body | unsupportedTy f.span "this function body"
  -- Falling off the end of a `void` method returns, as the converted program says.
  let body := if void then body ++ [.return_ (.literal .undefined f.span) f.span] else body
  let block ← checkStmts T s result body
  if block.falls then
    throw { code := "A2003", message := s!"'{f.name}' may finish without returning a value", span := f.span }
  if block.breaks || block.continues then
    throw { code := "A2003", message := "break or continue outside a loop or switch", span := f.span }
  pure { sig := { name := f.name, params, result, trivial := block.trivial, method := this.isSome, void },
         body := block }

/-- Names a named type's readable alias may not take: the functions' and methods', and the generated
declarations'. -/
def reservedNames (p : Parse.Program) : List String :=
  ["ast", "typed", "sigs", "erased", "wf", "bodies_ok", "ast_scoped", "denote_eq", "safety_eq", "ty", "sig",
    "body", "ne"] ++ p.functions.map (·.name) ++ p.classes.flatMap (fun c => c.methods.map (·.name))

def checkProgram (p : Parse.Program) : Checked (Types × List CheckedFn) := do
  let mut T ← Types.ofProgram p
  let reserved := reservedNames p
  T := { T with readable := T.named.filterMap fun (n, _) => if reserved.contains n then none else some n }
  let mut fns := []
  let mut out := []
  for f in p.functions do
    let c ← checkFunction T fns f
    fns := fns ++ [c.sig]
    out := out ++ [c]
  if let some c := p.classes[1]? then unsupportedTy c.span "a second class"
  if let some c := p.classes.head? then
    if let some ctor := c.constructor_ then unsupportedTy ctor.span "a constructor"
    let fields ← c.fields.mapM fun fld => match fld.value with
      | .newMap .string v sp => return (fld.name, Ty.map (← T.resolve sp 64 v))
      | _ => unsupportedTy fld.span "a field other than a Map with string keys"
    let σ := Ty.record (Fields.ofList fields)
    T := { T with named := T.named ++ [(c.name, σ)],
                  readable := if reserved.contains c.name then T.readable else T.readable ++ [c.name] }
    -- `new C()`: the state with every map empty.
    let initBody : List Parse.Stmt :=
      [.return_ (.record (c.fields.map fun fld => (fld.name, fld.value)) c.span) c.span]
    let block ← checkStmts T { fns, locals := [] } σ initBody
    let initFn : CheckedFn :=
      { sig := { name := s!"new {c.name}", params := [], result := σ, trivial := block.trivial }, body := block }
    fns := fns ++ [initFn.sig]
    out := out ++ [initFn]
    for m in ← orderMethods c.methods do
      let cm ← checkFunction T fns m (some σ)
      fns := fns ++ [cm.sig]
      out := out ++ [cm]
  pure (T, out)

/-! ## Printing the AST -/

def printLit : Lit → String
  | .undefined => ".undefined" | .null => ".null"
  | .bool b => s!"(.bool {b})"
  | .number n => s!"(.number {n})"
  | .bigint n => s!"(.bigint {n})"
  | .string s => s!"(.string {jsString s})"

def printUnOp : UnOp → String
  | .not => ".not" | .neg => ".neg"

def printBinOp : BinOp → String
  | .add => ".add" | .sub => ".sub" | .mul => ".mul" | .eq => ".eq" | .ne => ".ne"
  | .lt => ".lt" | .le => ".le" | .gt => ".gt" | .ge => ".ge" | .and => ".and" | .or => ".or"
  | .coalesce => ".coalesce" | .looseEq => ".looseEq" | .looseNe => ".looseNe"

partial def printExpr : Expr → String
  | .lit l => s!"(.lit {printLit l})"
  | .var x => s!"(.var {leanString x})"
  | .unary op e => s!"(.unary {printUnOp op} {printExpr e})"
  | .binary op a b => s!"(.binary {printBinOp op} {printExpr a} {printExpr b})"
  | .cond c a b => s!"(.cond {printExpr c} {printExpr a} {printExpr b})"
  | .call f args => s!"(.call {leanString f} [{", ".intercalate (args.map printExpr)}])"
  | .record es => "(.record [" ++ ", ".intercalate (es.map fun (f, e) =>
      "(" ++ (match f with | some f => s!"some {leanString f}" | none => "none") ++ s!", {printExpr e})") ++ "])"
  | .field e f => s!"(.field {printExpr e} {leanString f})"
  | .array es => "(.array [" ++ ", ".intercalate (es.map fun (sp, e) => s!"({sp}, {printExpr e})") ++ "])"
  | .index e i => s!"(.index {printExpr e} {printExpr i})"
  | .method e m args => s!"(.method {printExpr e} {leanString m} [{", ".intercalate (args.map printExpr)}])"
  | .arrow ps body => s!"(.arrow {ps.map leanString} {printExpr body})"
  | .newMap => ".newMap"
  | .stateGet f k => s!"(.stateGet {leanString f} {printExpr k})"
  | .stateHas f k => s!"(.stateHas {leanString f} {printExpr k})"
  | .stateSize f => s!"(.stateSize {leanString f})"
  | .stateKeys f => s!"(.stateKeys {leanString f})"
  | .stateValues f => s!"(.stateValues {leanString f})"
  | .callThis m args => s!"(.callThis {leanString m} [{", ".intercalate (args.map printExpr)}])"

mutual
  partial def printStmt (indent : String) : Stmt → String
    | .const x e => s!".const {leanString x} {printExpr e}"
    | .let_ x e => s!".let_ {leanString x} {printExpr e}"
    | .assign x e => s!".assign {leanString x} {printExpr e}"
    | .ret e => s!".ret {printExpr e}"
    | .ite c yes no =>
      s!".ite {printExpr c}\n{indent}  {printStmts (indent ++ "  ") yes}\n{indent}  {printStmts (indent ++ "  ") no}"
    | .block ss => s!".block {printStmts (indent ++ "  ") ss}"
    | .switch e cases =>
      let j := indent ++ "  "
      let printCase := fun ((label, body) : Option Expr × List Stmt) =>
        "(" ++ (match label with | some t => s!"some {printExpr t}" | none => "none") ++
          s!", {printStmts (j ++ "  ") body})"
      s!".switch {printExpr e} [\n{j}" ++ s!",\n{j}".intercalate (cases.map printCase) ++ "]"
    | .brk => ".brk"
    | .cont => ".cont"
    | .forOf x e body => s!".forOf {leanString x} {printExpr e} {printStmts (indent ++ "  ") body}"
    | .forEntries i x e body =>
      s!".forEntries {leanString i} {leanString x} {printExpr e} {printStmts (indent ++ "  ") body}"
    | .forRange i n body => s!".forRange {leanString i} {leanString n} {printStmts (indent ++ "  ") body}"
    | .stateSet f k v => s!".stateSet {leanString f} {printExpr k} {printExpr v}"
    | .stateDelete f k => s!".stateDelete {leanString f} {printExpr k}"
    | .callThis m args => s!".callThis {leanString m} [{", ".intercalate (args.map printExpr)}]"

  partial def printStmts (indent : String) (ss : List Stmt) : String :=
    if ss.isEmpty then "[]" else
      s!"[\n{indent}  " ++ s!",\n{indent}  ".intercalate (ss.map (printStmt (indent ++ "  "))) ++ "]"
end

def printFunction (fn : Function) : String :=
  "{ name := " ++ leanString fn.name ++ s!", params := {fn.params.map leanString}, body := " ++
    printStmts "    " fn.body ++ (if fn.method then ", method := true }" else " }")

/-! ## The generated file -/

def sigName (f : String) : String := s!"sig.{ident f}"

/-- Readable names for the named types: an alias `«T»` for the denoted type, written as the product,
sum or `Fin` it is; for a record, an accessor `«T».«f»` per field; for a literal union, a constant
`«T».«lit»` per literal; for a union of records, a payload type `«T».Variant.«tag»` with its
accessors, and a constructor `«T».«tag»` per variant.
All are reducible and in the simp set `readable`, so they unfold to the projections, numerals and
injections readable definitions use. -/
def readableNames (T : Types) : String := Id.run do
  -- A named type comes after the named types inside it, which its alias mentions.
  let inside (σ τ : Ty) : Bool := σ != τ && ((printTy τ).splitOn (printTy σ)).length > 1
  let mut order : List (String × Ty) := []
  let mut todo := T.named.filter fun (n, _) => T.readable.contains n
  while !todo.isEmpty do
    let ready := todo.filter fun (_, τ) => !todo.any fun (_, σ) => inside σ τ
    let next := if ready.isEmpty then todo else ready
    order := order ++ next
    todo := todo.filter fun (n, _) => !next.any (·.1 == n)
  let mut out := ""
  for (n, τ) in order do
    let N := ident n
    -- Accessors `«T».«f»`, and when no field takes their names, a constructor `«T».mk` and setters `«T».«withF»`.
    let accessors (owner : String) (fs : Fields) : String := Id.run do
      let fields := Fields.toList fs
      let mut acc := ""
      for (k, (f, σ)) in fields.zipIdx.map (fun ((f, σ), k) => (k, (f, σ))) do
        acc := acc ++ s!"@[reducible, readable] def {owner}.{ident f} (r : {owner}) : {T.lean σ} := {projText "r" k}\n"
      if namesFree fs then
        let binders := " ".intercalate (fields.map fun (f, σ) => s!"({ident f} : {T.lean σ})")
        let tuple := "(" ++ ", ".intercalate (fields.map (ident ·.1) ++ ["()"]) ++ ")"
        acc := acc ++ s!"@[reducible, readable] def {owner}.mk {binders} : {owner} := {tuple}\n"
        for (k, (f, σ)) in fields.zipIdx.map (fun ((f, σ), k) => (k, (f, σ))) do
          acc := acc ++ s!"@[reducible, readable] def {owner}.{ident (setterName f)} (r : {owner}) (v : {T.lean σ}) : " ++
            s!"{owner} := {tupleSetText "r" k fields.length "v"}\n"
      return acc
    -- The fields' product, with their readable names (so that `x.order.map (·.index)` works).
    let product (fs : Fields) : String :=
      (Fields.toList fs).foldr (fun (_, σ) acc => s!"{atomText (T.lean σ)} × {acc}") "Unit"
    let doc := s!"\n/-- The source's `{n}`. -/\n"
    match τ with
    | .record fs => out := out ++ doc ++ s!"abbrev {N} : Type := {product fs}\n" ++ accessors N fs
    | .lits a as =>
      out := out ++ doc ++ s!"abbrev {N} : Type := Fin {as.length + 1}\n"
      for (lit, i) in (a :: as).zipIdx do
        if let some l := litName lit then
          out := out ++ s!"@[reducible, readable] def {N}.{ident l} : {N} := ({i} : Fin {as.length + 1})\n"
    | .union _ vs =>
      let variants := Variants.toList vs
      let mut payloads : List String := []
      let mut decls := ""
      for ((t, fs), i) in variants.zipIdx do
        let some tn := tagName t | payloads := payloads ++ [s!"({product fs})"]; continue
        -- Constructors, usable as patterns: of nothing, of a variant's one field, or of its payload.
        let ctor := s!"@[reducible, readable, match_pattern] def {N}.{ident tn}"
        match Fields.toList fs with
        | [] =>
          payloads := payloads ++ ["Unit"]
          decls := decls ++ s!"{ctor} : {N} := {injText i variants.length "()"}\n"
        | fields =>
          let V := s!"{N}.Variant.{ident tn}"
          payloads := payloads ++ [V]
          out := out ++ s!"abbrev {V} : Type := {product fs}\n" ++ accessors V fs
          match fields with
          | [(f, σ)] =>
            decls := decls ++ s!"{ctor} ({ident f} : {T.lean σ}) : {N} := {injText i variants.length s!"({ident f}, ())"}\n"
          | _ => decls := decls ++ s!"{ctor} (x : {V}) : {N} := {injText i variants.length "x"}\n"
      out := out ++ doc ++ s!"abbrev {N} : Type := {" ⊕ ".intercalate payloads}\n" ++ decls
    | _ => out := out ++ doc ++ s!"abbrev {N} : Type := ty.{N}.denote\n"
  return out

/-- The Lean source for a checked file: the AST, the typed program, readable
definitions, and per-function source theorems. -/
def printFile (source namespace_ : String) (ast : Program) (T : Types) (fns : List CheckedFn) : String := Id.run do
  -- A line comment: a path may contain `/-`, which would open a block comment.
  let name := ((source.splitOn "/").getLast?.getD source).map fun c => if c == '\n' || c == '\r' then ' ' else c
  let mut out := s!"import Ariadne.Proof.Adequacy\nimport Ariadne.Lib.Readable\n\n-- Generated by ariadne from {name}. Do not edit.\n\n"
  out := out ++ s!"namespace {namespace_}\nopen Ariadne\n\nset_option maxRecDepth 8192\nset_option linter.unusedVariables false\n\n"
  out := out ++ "/-- The source file in the model's syntax. -/\nnoncomputable def ast : Program := [\n  " ++
    ",\n  ".intercalate (ast.map printFunction) ++ "]\n\n"
  for (n, τ) in T.named do
    out := out ++ s!"noncomputable abbrev ty.{ident n} : Ty := {printTy τ}\n"
  out := out ++ readableNames T
  if !T.named.isEmpty then out := out ++ "\n"
  for fn in fns do
    let s := fn.sig
    let ctx := "[" ++ ", ".intercalate (s.params.map fun (x, τ) => s!"({leanString x}, {T.print τ})") ++ "]"
    let kind := if s.method then s!", method := true, void := {s.void}" else ""
    out := out ++ s!"noncomputable def {sigName s.name} : Sig := " ++ "{ name := " ++ leanString s.name ++
      s!", params := {ctx}, result := {T.print s.result}, trivial := {s.trivial}{kind} " ++ "}\n"
  out := out ++ "\n"
  let nes := (fns.foldl (fun acc fn => acc ++ collectNe fn.body.typed) []).eraseDups
  for (a, b) in nes do
    out := out ++ s!"theorem ne.{ident a}.{ident b} : ({leanString a} : String) ≠ {leanString b} := by decide\n"
  if !nes.isEmpty then out := out ++ "\n"
  let mut earlier : List String := []
  for fn in fns do
    let s := fn.sig
    let φ := "[" ++ ", ".intercalate (earlier.map sigName) ++ "]"
    out := out ++ s!"noncomputable def body.{ident s.name} : TStmts {φ} {sigName s.name}.params {sigName s.name}.result :=\n  " ++
      fn.body.typed ++ "\n\n"
    earlier := s.name :: earlier
  let all := "[" ++ ", ".intercalate (earlier.map sigName) ++ "]"
  let program := fns.foldl (fun acc fn => s!"(.cons {sigName fn.sig.name} body.{ident fn.sig.name} {acc})") ".nil"
  out := out ++ s!"noncomputable abbrev sigs : Sigs := {all}\n\nnoncomputable def typed : TProgram sigs :=\n  {program}\n\n"
  out := out ++ "theorem erased : typed.erase = ast := by kernel_rfl\n\ntheorem bodies_ok : typed.bodiesOk = true := by decide +kernel\n\n" ++
    "theorem ast_scoped : ast.scoped = true := by decide +kernel\n\n" ++
    "theorem wf : typed.WF := TProgram.wf_of typed erased bodies_ok ast_scoped\n\n"
  out := out ++ "/-! ## Readable definitions -/\n\n"
  for fn in fns do
    let s := fn.sig
    let params := " ".intercalate (s.params.map fun (x, τ) => s!"({ident x} : {T.lean τ})")
    let dflt := s!"(Ty.default {T.print s.result})"
    out := out ++ s!"def {ident s.name} {params} : {T.lean s.result} :=\n  " ++
      fn.body.readable "  " ⟨fun _ => dflt, fun _ => dflt, fun _ => dflt⟩ ++ "\n\n"
    if !s.trivial then
      out := out ++ s!"/-- The inputs on which `{s.name}` stays within what the model covers. -/\n"
      out := out ++ s!"def {ident s.name}.safe {params} : Bool :=\n  " ++
        fn.body.safe "  " ⟨fun _ => "true", fun _ => "true", fun _ => "true"⟩ ++ "\n\n"
  out := out ++ "/-! ## Denotation

Each body is checked against its readable definition with the earlier functions'
readable definitions as its environment, so no check unfolds a callee. -/\n\n"
  let tupleOf (names : List String) (suffix : String) : String :=
    "(" ++ ", ".intercalate (names.map (s!"{ident ·}.{suffix}") ++ ["()"]) ++ ")"
  let mut prior : List String := []
  for fn in fns do
    let s := fn.sig
    let projections := (List.range s.params.length).map fun k => projText "xs" k
    let applied := if s.params.isEmpty then ident s.name else " ".intercalate (ident s.name :: projections)
    out := out ++ s!"noncomputable def {ident s.name}.uncurried : {sigName s.name}.denote := fun xs => {applied}\n\n"
    if s.trivial then
      out := out ++ s!"/-- Trivially safe: every input is in what the model covers. -/\n"
      out := out ++ s!"noncomputable def {ident s.name}.safety : {sigName s.name}.params.denote → Bool := fun _ => true\n\n"
    else
      let safeApplied := " ".intercalate (s!"{ident s.name}.safe" :: projections)
      out := out ++ s!"noncomputable def {ident s.name}.safety : {sigName s.name}.params.denote → Bool := fun xs => {safeApplied}\n\n"
    out := out ++ s!"theorem {ident s.name}.body_eq :\n    body.{ident s.name}.denoteFn {tupleOf prior "uncurried"} = {ident s.name}.uncurried := by\n  kernel_rfl\n\n"
    out := out ++ s!"theorem {ident s.name}.safe_eq :\n    body.{ident s.name}.safeFn {tupleOf prior "uncurried"} {tupleOf prior "safety"} = {ident s.name}.safety := by\n  kernel_rfl\n\n"
    prior := s.name :: prior
  let proof := fns.foldl (fun acc fn => s!"(TProgram.denote_cons {acc} {ident fn.sig.name}.body_eq)") "rfl"
  let safetyProof := (fns.foldl (fun (acc, den) fn =>
      (s!"(TProgram.safety_cons {den} {acc} {ident fn.sig.name}.safe_eq)",
       s!"(TProgram.denote_cons {den} {ident fn.sig.name}.body_eq)")) ("rfl", "rfl")).1
  out := out ++ s!"theorem denote_eq : typed.denote = {tupleOf prior "uncurried"} :=\n  {proof}\n\n"
  out := out ++ s!"theorem safety_eq : typed.safety = {tupleOf prior "safety"} :=\n  {safetyProof}\n\n"
  out := out ++ "/-! ## Source theorems -/\n\n"
  let n := fns.length
  for (fn, i) in fns.zipIdx do
    let s := fn.sig
    let path := fnPath (n - 1 - i)
    let fvar := s!"({path} : FVar sigs {leanString s.name} {sigName s.name})"
    let binders := " ".intercalate (s.params.map fun (x, τ) => s!"({ident x} : {T.lean τ})")
    let names := " ".intercalate (s.params.map (ident ·.1))
    let tuple := "(" ++ ", ".intercalate (s.params.map (ident ·.1) ++ ["()"]) ++ ")"
    let call := if s.params.isEmpty then ident s.name else s!"{ident s.name} {names}"
    let safeHyp := if s.trivial then "" else
      s!"\n    (safe' : {" ".intercalate (s!"{ident s.name}.safe" :: s.params.map (ident ·.1))} = true)"
    let safeArg := if s.trivial then "rfl" else "safe'"
    -- Binders are primed: JavaScript names cannot clash with them.
    if s.void then
      out := out ++ s!"/-- Every run of `{s.name}` on a state and arguments representing its inputs converges to a\nstate representing the readable definition's result. -/\n"
      out := out ++ s!"theorem {ident s.name}.source {binders} (this' : JSValue) (vs' : List JSValue)\n    (args' : ArgsRep {sigName s.name}.params (this' :: vs') {tuple}){safeHyp} :\n"
      out := out ++ s!"    ∃ w' t', Converges (fun fuel' => runMethod ast fuel' {leanString s.name} this' vs') (.ok (w', t')) ∧\n      Ty.Rep {T.print s.result} t' ({call}) :=\n"
      out := out ++ s!"  source_state_of erased wf denote_eq safety_eq {fvar} rfl {tuple} this' vs' args' {safeArg}\n\n"
    else
      out := out ++ s!"/-- Every run of `{s.name}` on arguments representing its inputs converges to a value\nrepresenting the readable definition's result. -/\n"
      out := out ++ s!"theorem {ident s.name}.source {binders} (vs' : List JSValue)\n    (args' : ArgsRep {sigName s.name}.params vs' {tuple}){safeHyp} :\n"
      out := out ++ s!"    ∃ w', Converges (fun fuel' => run ast fuel' {leanString s.name} vs') (.ok w') ∧\n      Ty.Rep {T.print s.result} w' ({call}) :=\n"
      out := out ++ s!"  source_of erased wf denote_eq safety_eq {fvar} rfl {tuple} vs' args' {safeArg}\n\n"
  out := out ++ s!"end {namespace_}\n"
  return out

/-- A type as JSON, for test generators. -/
partial def tyJson : Ty → String
  | .bool => "{\"t\":\"bool\"}" | .int => "{\"t\":\"bigint\"}" | .number => "{\"t\":\"number\"}"
  | .string => "{\"t\":\"string\"}"
  | .tag (.str s) => "{\"t\":\"tag\",\"value\":" ++ s!"{s.map (·.toNat)}" ++ "}"
  | .tag (.bool b) => "{\"t\":\"tag\",\"bool\":" ++ toString b ++ "}"
  | .lits a as => "{\"t\":\"lits\",\"values\":[" ++ ",".intercalate ((a :: as).map fun s => s!"{s.map (·.toNat)}") ++ "]}"
  | .option n τ => "{\"t\":\"option\",\"nullish\":\"" ++ (match n with | .undef => "undef" | .null => "null" | .both => "both") ++
      "\",\"of\":" ++ tyJson τ ++ "}"
  | .record fs => "{\"t\":\"record\",\"fields\":" ++ fieldsJson fs ++ "}"
  | .union key vs => "{\"t\":\"union\",\"key\":" ++ leanString key ++ ",\"variants\":[" ++
      ",".intercalate ((Variants.toList vs).map fun (t, fs) => "{\"tag\":" ++ tyJson (.tag t) ++ ",\"fields\":" ++ fieldsJson fs ++ "}") ++ "]}"
  | .array τ => "{\"t\":\"array\",\"of\":" ++ tyJson τ ++ "}"
  | .map τ => "{\"t\":\"map\",\"of\":" ++ tyJson τ ++ "}"
where
  fieldsJson (fs : Fields) : String :=
    "[" ++ ",".intercalate ((Fields.toList fs).map fun (f, τ) => "[" ++ leanString f ++ "," ++ tyJson τ ++ "]") ++ "]"

/-- Each function's name, whether it is exported, and its parameter and result types, as JSON lines.
A class's constructor (`new C`) and methods are marked with the class (a method's
parameters start with the state). -/
def signatures (text : String) : Checked (List String) := do
  let parsed ← Parse.parse text
  let (_, fns) ← checkProgram parsed
  let cls := (parsed.classes.head?.map fun c => leanString c.name).getD "null"
  return fns.map fun c =>
    let exported := parsed.functions.any fun f => f.name == c.sig.name && f.exported
    let classSide := c.sig.method || c.sig.name.startsWith "new "
    "{\"name\":" ++ leanString c.sig.name ++ ",\"exported\":" ++ toString (exported || classSide) ++
      ",\"class\":" ++ (if classSide then cls else "null") ++ ",\"method\":" ++ toString c.sig.method ++
      ",\"void\":" ++ toString c.sig.void ++ ",\"params\":[" ++
      ",".intercalate (c.sig.params.map (tyJson ·.2)) ++ "],\"result\":" ++ tyJson c.sig.result ++ "}"

/-- Parse, convert and check a TypeScript file, returning the generated Lean source. -/
def translate (source namespace_ text : String) : Checked String := do
  let parsed ← Parse.parse text
  let ast ← convertProgram parsed
  let (T, fns) ← checkProgram parsed
  pure (printFile source namespace_ ast T fns)

end Ariadne.Front
