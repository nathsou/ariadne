import V2.Front.Convert
import V2.Typed.Syntax

/-!
# Type checking and printing

Untrusted. Builds, as Lean source, the typed program whose erasure must equal the
converted AST, the readable definitions that must equal its denotation, and the
per-function source theorems. The kernel checks all of it when the generated file
is compiled, so a bug here makes that file fail to check; it cannot produce a
wrong theorem.
-/

namespace V2.Front
open V2.Parse (Diagnostic Checked Span)

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
  /-- Lean syntax for a type. -/
  partial def printTy : Ty → String
    | .bool => ".bool" | .int => ".int" | .number => ".number" | .string => ".string"
    | .tag t => s!"(.tag {printTag t})"
    | .lits a as => s!"(.lits {jsString a} [{", ".intercalate (as.map jsString)}])"
    | .option n τ => s!"(.option {printNullish n} {printTy τ})"
    | .record fs => s!"(.record {printFields fs})"
    | .union key vs => s!"(.union {leanString key} {printVariants vs})"
    | .array τ => s!"(.array {printTy τ})"

  partial def printFields : Fields → String
    | .nil => ".nil"
    | .cons f τ rest => s!"(.cons {leanString f} {printTy τ} {printFields rest})"

  partial def printVariants : Variants → String
    | .one t fs => s!"(.one {printTag t} {printFields fs})"
    | .cons t fs rest => s!"(.cons {printTag t} {printFields fs} {printVariants rest})"
end

def _root_.V2.Ty.ts : Ty → String
  | .bool => "boolean" | .int => "bigint" | .number => "number" | .string => "string"
  | .tag t => tagLitTS t | .lits .. => "a string literal union" | .option .. => "an optional"
  | .record _ => "a record" | .union .. => "a union" | .array _ => "an array"

/-- Named types (aliases and interfaces) and their resolved forms. -/
structure Types where
  aliases : List (String × Parse.Ty)
  /-- Resolved named types, printed as `ty.«Name»`. -/
  named : List (String × Ty) := []

def Types.print (T : Types) (τ : Ty) : String :=
  match T.named.find? (·.2 == τ) with
  | some (n, _) => s!"ty.{ident n}"
  | none => printTy τ

/-- The Lean type of a denoted value. -/
def Types.lean (T : Types) : Ty → String
  | .bool => "Bool" | .int => "Int" | .number => "Int" | .string => "JSString"
  | τ => match T.named.find? (·.2 == τ) with
    | some (n, _) => s!"ty.{ident n}.denote"
    | none => s!"(({printTy τ} : Ty)).denote"

def Fields.toList : Fields → List (String × Ty)
  | .nil => []
  | .cons f τ rest => (f, τ) :: Fields.toList rest

def Fields.ofList : List (String × Ty) → Fields
  | [] => .nil
  | (f, τ) :: rest => .cons f τ (Fields.ofList rest)

def Variants.toList : Variants → List (TagLit × Fields)
  | .one t fs => [(t, fs)]
  | .cons t fs rest => (t, fs) :: Variants.toList rest

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
  deriving Inhabited

structure Scope where
  fns : List FnSig
  /-- Bindings in scope, innermost first, with their current (narrowed) types. -/
  locals : List (String × Ty)

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

/-- A checked expression as typed syntax, and as a readable Lean term. -/
structure Out where
  ty : Ty
  typed : String
  readable : String
  atomic : Bool := false
  deriving Inhabited

def Out.term (o : Out) : String := if o.atomic then o.readable else s!"({o.readable})"

/-- A variable narrowed by a test, with how its narrowed value re-embeds. -/
structure Narrowed where
  index : Nat
  name : String
  wide : Ty
  narrow : Ty
  /-- Readable re-embedding of the narrowed value named `«x»`. -/
  embed : String

def Narrowed.wrap (n : Narrowed) (k : String → String) : String → String :=
  fun i => s!"let {ident n.name} := {n.embed}\n{i}{k i}"

def vrec' (key : String) (t : TagLit) (fs : Fields) : Ty := .record (.cons key (.tag t) fs)

/-- Use a value of type `out.ty` at type `τ`: equal, or a no-op embedding. -/
def coerce (T : Types) (span : Span) (out : Out) (τ : Ty) : Checked Out := do
  if out.ty == τ then return out
  match τ with
  | .option n σ =>
    if out.ty == σ then
      return { ty := τ, typed := s!"(.widen (.some {printNullish n} {T.print σ}) {out.typed})",
               readable := s!"some {out.term}" }
    mismatch span s!"{out.ty.ts} where {τ.ts} is expected"
  | .union key vs =>
    let variants := Variants.toList vs
    match variants.findIdx? (fun (t, fs) => out.ty == vrec' key t fs) with
    | some i =>
      return { ty := τ, typed := s!"(.widen (.variant {vidxPath i variants.length}) {out.typed})",
               readable := injText i variants.length s!"{out.term}.2" }
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
    | .literal (.string units) _ =>
      match expected with
      | some (.tag (.str u)) =>
        if u == units then
          return { ty := .tag (.str u), typed := s!"(.tagLit (.str {jsString u}))", readable := "()", atomic := true }
        return { ty := .string, typed := s!"(.str {jsString units})", readable := jsString units, atomic := true }
      | some τ@(.lits a as) =>
        match (a :: as).findIdx? (· == units) with
        | some i => return { ty := τ, typed := s!"(.litIn {jsString a} [{", ".intercalate (as.map jsString)}] {i})",
                             readable := s!"({i} : Fin {as.length + 1})", atomic := true }
        | none => mismatch e.span "a string outside the literal union"
      | _ => return { ty := .string, typed := s!"(.str {jsString units})", readable := jsString units, atomic := true }
    | .literal .undefined span =>
      match expected with
      | some τ@(.option n σ) =>
        if !n.undef? then mismatch span s!"undefined where {τ.ts} admits only null"
        return { ty := τ, typed := s!"(.undef {printNullish n} {T.print σ} (by decide))", readable := "none",
                 atomic := true }
      | _ => mismatch span "undefined needs an optional type here"
    | .literal .null span =>
      match expected with
      | some τ@(.option n σ) =>
        if !n.null? then mismatch span s!"null where {τ.ts} admits only undefined"
        return { ty := τ, typed := s!"(.null {printNullish n} {T.print σ} (by decide))", readable := "none",
                 atomic := true }
      | _ => mismatch span "null needs an optional type here"
    | .literal _ span => unsupportedTy span "this literal (number literals arrive with L2)"
    | .var x span =>
      match s.lookup x with
      | some (i, τ) => return { ty := τ, typed := s!"(.var {s.varPath i})", readable := ident x, atomic := true }
      | none => throw { code := "A2001", message := s!"unknown variable '{x}'", span }
    | .unary op a span => do
      let a ← inferExpr T s a none
      match op, a.ty with
      | "!", .bool => return { ty := .bool, typed := s!"(.not {a.typed})", readable := s!"!{a.term}" }
      | "-", .int => return { ty := .int, typed := s!"(.neg {a.typed})", readable := s!"(-{a.term})", atomic := true }
      | op, τ => mismatch span s!"'{op}' does not apply to {τ.ts}"
    | .binary op a b span => checkBinary T s op a b span expected
    | .conditional c a b span =>
      match nullTestVar c with
      | some (x, isNull) => do
        let (n, path) ← s.nullNarrowing span x
        let narrowed := s.narrow n.index n.narrow
        let (sa, sb) := if isNull then (s, narrowed) else (narrowed, s)
        let a ← match expected with
          | some τ => checkExpr T sa a (some τ)
          | none => inferExpr T sa a none
        let b ← checkExpr T sb b (some a.ty)
        let ctor := if isNull then "condNull" else "condNotNull"
        let readable := if isNull then
            s!"match {ident x} with | none => {a.readable} | some {ident x} => {b.readable}"
          else s!"match {ident x} with | some {ident x} => {a.readable} | none => {b.readable}"
        return { ty := a.ty, typed := s!"(.{ctor} {path} (by decide) {a.typed} {b.typed})", readable }
      | none => do
        let c ← checkExpr T s c (some .bool)
        let a ← match expected with
          | some τ => checkExpr T s a (some τ)
          | none => inferExpr T s a none
        let b ← checkExpr T s b (some a.ty)
        return { ty := a.ty, typed := s!"(.cond {c.typed} {a.typed} {b.typed})",
                 readable := s!"if {c.readable} then {a.readable} else {b.readable}" }
    | .call (.var f _) args span => do
      let some j := s.fns.findIdx? (·.name == f)
        | throw { code := "A2001", message := s!"'{f}' is not a function declared earlier", span }
      if s.locals.any (·.1 == f) then mismatch span s!"'{f}' is shadowed by a local"
      let sig := s.fns[j]!
      if args.length > sig.params.length then mismatch span s!"'{f}' takes {sig.params.length} arguments"
      let given ← (args.zip sig.params).mapM fun (a, (_, τ)) => checkExpr T s a (some τ)
      let omitted := sig.params.drop args.length
      if !omitted.all (fun (_, τ) => τ matches .option .undef _ | .option .both _) then
        mismatch span s!"'{f}' needs {sig.params.length} arguments"
      let typedArgs := given.foldr (fun a acc => s!"(.cons {a.typed} {acc})")
        (if omitted.isEmpty then ".nil" else "(.omitted (by decide))")
      let readableArgs := given.map (·.term) ++ omitted.map fun _ => "none"
      let readable := if readableArgs.isEmpty then ident f else " ".intercalate (ident f :: readableArgs)
      return { ty := sig.result, typed := s!"(.call {fnPath (s.fns.length - 1 - j)} (by decide) {typedArgs})",
               readable, atomic := readableArgs.isEmpty }
    | .member a f span => do
      let a ← inferExpr T s a none
      match a.ty with
      | .record fs =>
        let fields := Fields.toList fs
        match fields.findIdx? (·.1 == f) with
        | some k =>
          if protoName f then mismatch span s!"'{f}' is an Object.prototype property"
          return { ty := fields[k]!.2, typed := s!"(.field {a.typed} {fidxPath k} (by decide))",
                   readable := projText a.term k }
        | none => mismatch span s!"no field '{f}'"
      | τ => mismatch span s!"field '{f}' of {τ.ts}"
    | .record entries span => do
      let some τ := expected | mismatch span "an object literal needs a known type here"
      checkRecord T s entries span τ
    | e => unsupportedTy e.span "this expression"

  partial def checkBinary (T : Types) (s : Scope) (op : String) (a b : Parse.Expr) (span : Span)
      (_expected : Option Ty) : Checked Out := do
    match op with
    | "&&" | "||" => do
      let a ← checkExpr T s a (some .bool)
      let b ← checkExpr T s b (some .bool)
      return { ty := .bool, typed := s!"(.{if op == "&&" then "and" else "or"} {a.typed} {b.typed})",
               readable := s!"{a.term} {op} {b.term}" }
    | "==" | "!=" => do
      let .literal .null _ := b | unsupportedTy span s!"'{op}' other than against null"
      let a ← inferExpr T s a none
      let .option _ σ := a.ty | mismatch span s!"'{op} null' on {a.ty.ts}"
      if !σ.nonNullish then mismatch span "a nested optional"
      let (ctor, readable) := if op == "==" then ("isNull", s!"{a.term}.isNone") else ("notNull", s!"{a.term}.isSome")
      return { ty := .bool, typed := s!"(.{ctor} (by decide) {a.typed})", readable }
    | "??" => do
      let a ← inferExpr T s a none
      let .option _ σ := a.ty | mismatch span s!"'??' on {a.ty.ts}"
      if !σ.nonNullish then mismatch span "a nested optional"
      let b ← checkExpr T s b (some σ)
      return { ty := σ, typed := s!"(.coalesce (by decide) {a.typed} {b.typed})",
               readable := s!"match {a.readable} with | some v' => v' | none => {b.readable}" }
    | "===" | "!==" => do
      -- Type a literal operand against the other side.
      let (a, b) ← match a with
        | .literal .. => do let b ← inferExpr T s b none; pure (← checkExpr T s a (some b.ty), b)
        | _ => do let a ← inferExpr T s a none; pure (a, ← checkExpr T s b (some a.ty))
      if !a.ty.prim then mismatch span s!"'{op}' on {a.ty.ts} (objects compare by identity)"
      let neg := op == "!=="
      return { ty := .bool, typed := s!"(.{if neg then "ne" else "eq"} (by decide) {a.typed} {b.typed})",
               readable := s!"{a.term} {if neg then "!=" else "=="} {b.term}" }
    | _ => do
      let a ← inferExpr T s a none
      let b ← checkExpr T s b (some a.ty)
      let mk (ty : Ty) (ctor readable : String) : Out := { ty, typed := s!"(.{ctor} {a.typed} {b.typed})", readable }
      match op, a.ty with
      | "+", .int => pure (mk .int "add" s!"{a.term} + {b.term}")
      | "-", .int => pure (mk .int "sub" s!"{a.term} - {b.term}")
      | "*", .int => pure (mk .int "mul" s!"{a.term} * {b.term}")
      | "+", .string => pure (mk .string "concat" s!"{a.term} ++ {b.term}")
      | "<", .int => pure (mk .bool "lt" s!"decide ({a.term} < {b.term})")
      | "<=", .int => pure (mk .bool "le" s!"decide ({a.term} ≤ {b.term})")
      | ">", .int => pure (mk .bool "gt" s!"decide ({a.term} > {b.term})")
      | ">=", .int => pure (mk .bool "ge" s!"decide ({a.term} ≥ {b.term})")
      | "<", .string => pure (mk .bool "slt" s!"strLt {a.term} {b.term}")
      | "<=", .string => pure (mk .bool "sle" s!"strLe {a.term} {b.term}")
      | ">", .string => pure (mk .bool "sgt" s!"strLt {b.term} {a.term}")
      | ">=", .string => pure (mk .bool "sge" s!"strLe {b.term} {a.term}")
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
      coerce T span r (.union key vs)
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
            | none => (s!"(.keep (by decide) {accU})", projText "r'" k :: accR)) (".nil", [])
        return { ty := τ, typed := s!"(.update {r.typed} {typedEntries} {upd} (by decide))",
                 readable := s!"let r' := {r.readable}; ({", ".intercalate (readable ++ ["()"])})" }
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
              | .option .undef _ | .option .both _ => pure (s!"(.absent (by decide) {accS})", "none" :: accR)
              | _ => mismatch span s!"the literal has no '{f}' field") (".nil", [])
        return { ty := τ, typed := s!"(.record {typedEntries} {sel.1} (by decide))",
                 readable := "(" ++ ", ".intercalate (sel.2 ++ ["()"]) ++ ")" }
    | τ => mismatch span s!"an object literal where {τ.ts} is expected"
end

/-! ## Statements -/

/-- Readable continuations, rendered at the indentation where they are placed. -/
structure KText where
  normal : String → String
  brk : String → String
  cont : String → String

def KText.wrap (k : KText) (n : Narrowed) : KText := ⟨n.wrap k.normal, n.wrap k.brk, n.wrap k.cont⟩

/-- A checked statement list: typed syntax, a readable printer taking the
continuations' text, and how it can end. -/
structure Block where
  typed : String
  readable : (indent : String) → KText → String
  falls : Bool
  breaks : Bool
  continues : Bool

def blockNil : Block where
  typed := ".nil"
  readable i k := k.normal i
  falls := true
  breaks := false
  continues := false

instance : Inhabited Block := ⟨blockNil⟩

def declare (s : Scope) (span : Span) (x : String) (τ : Ty) : Checked Scope := do
  if s.locals.any (·.1 == x) || s.fns.any (·.name == x) then
    throw { code := "A2004", message := s!"'{x}' shadows a declaration in scope", span,
            help := some "Rename it: the model requires names in scope to be distinct." }
  pure { s with locals := (x, τ) :: s.locals }

/-- An `if` branch's statements. -/
def branchStmts : Parse.Stmt → List Parse.Stmt
  | .block ss _ => ss
  | s => [s]

/-- Readable `switch` arms: nested matches on the union's sum, each binding the
narrowed variable to the variant's record (`((), fields)`). -/
def switchArms (x : String) (arms : List (Block × Narrowed)) (k : KText) (scrut ind : String) : String :=
  match arms with
  | [] => ""
  | [(b, n)] => s!"let {ident x} := ((), {scrut})\n{ind}{b.readable ind (k.wrap n)}"
  | (b, n) :: more =>
    let j := ind ++ "  "
    s!"match {scrut} with\n{ind}| Sum.inl p' =>\n{j}let {ident x} := ((), p')\n{j}{b.readable j (k.wrap n)}\n" ++
      s!"{ind}| Sum.inr p' =>\n{j}{switchArms x more k "p'" j}"

mutual
  partial def checkStmts (T : Types) (s : Scope) (result : Ty) : List Parse.Stmt → Checked Block
    | [] => pure blockNil
    | .let_ false x annotation e span :: rest => do
      let expected ← annotation.mapM (T.resolve span 64)
      let v ← checkExpr T s e expected
      let rest ← checkStmts T (← declare s span x v.ty) result rest
      pure { typed := s!"(.const {leanString x} {v.typed}\n  {rest.typed})",
             readable := fun i k => s!"let {ident x} := {v.readable}\n{i}{rest.readable i k}",
             falls := rest.falls, breaks := rest.breaks, continues := rest.continues }
    | .return_ e _ :: rest => do
      let v ← checkExpr T s e (some result)
      let rest ← checkStmts T s result rest
      pure { typed := s!"(.ret {v.typed} {rest.typed})", readable := fun _ _ => v.readable,
             falls := false, breaks := false, continues := false }
    | .break_ _ :: rest => do
      let rest ← checkStmts T s result rest
      pure { typed := s!"(.brk {rest.typed})", readable := (fun i k => k.brk i), falls := false, breaks := true,
             continues := false }
    | .block body _ :: rest => do
      let body ← checkStmts T s result body
      let rest ← checkStmts T s result rest
      pure { typed := s!"(.block {body.typed}\n  {rest.typed})",
             readable := fun i k => body.readable i { k with normal := fun j => rest.readable j k },
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
        pure { typed := s!"(.ite {c.typed}\n  {yes.typed}\n  {no.typed}\n  {rest.typed})",
               readable := fun i k =>
                 let j := i ++ "  "
                 let k' := { k with normal := fun j' => rest.readable j' k }
                 s!"if {c.readable} then\n{j}{yes.readable j k'}\n{i}else\n{j}{no.readable j k'}",
               falls := (yes.falls || no.falls) && rest.falls,
               breaks := yes.breaks || no.breaks || ((yes.falls || no.falls) && rest.breaks),
               continues := yes.continues || no.continues || ((yes.falls || no.falls) && rest.continues) }
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
        return { typed := s!"(.ifNullExit {path} (by decide)\n  {yes.typed}\n  {rest.typed})",
                 readable := fun i k =>
                   let j := i ++ "  "
                   s!"match {ident x} with\n{i}| none =>\n{j}{yes.readable j k}\n{i}| some {ident x} =>\n{j}{rest.readable j (k.wrap n)}",
                 falls := rest.falls, breaks := yes.breaks || rest.breaks,
                 continues := yes.continues || rest.continues }
      let no ← checkStmts T narrowed result noSs
      let rest ← checkStmts T s result rest
      return { typed := s!"(.ifNull {path} (by decide)\n  {yes.typed}\n  {no.typed}\n  {rest.typed})",
               readable := fun i k =>
                 let j := i ++ "  "
                 let k' := { k with normal := fun j' => rest.readable j' k }
                 s!"match {ident x} with\n{i}| none =>\n{j}{yes.readable j k'}\n{i}| some {ident x} =>\n{j}{no.readable j (k'.wrap n)}",
               falls := (yes.falls || no.falls) && rest.falls,
               breaks := yes.breaks || no.breaks || ((yes.falls || no.falls) && rest.breaks),
               continues := yes.continues || no.continues || ((yes.falls || no.falls) && rest.continues) }
    else
      let yes ← checkStmts T narrowed result yesSs
      let no ← checkStmts T s result noSs
      let rest ← checkStmts T s result rest
      return { typed := s!"(.ifNotNull {path} (by decide)\n  {yes.typed}\n  {no.typed}\n  {rest.typed})",
               readable := fun i k =>
                 let j := i ++ "  "
                 let k' := { k with normal := fun j' => rest.readable j' k }
                 s!"match {ident x} with\n{i}| some {ident x} =>\n{j}{yes.readable j (k'.wrap n)}\n{i}| none =>\n{j}{no.readable j k'}",
               falls := (yes.falls || no.falls) && rest.falls,
               breaks := yes.breaks || no.breaks || ((yes.falls || no.falls) && rest.breaks),
               continues := yes.continues || no.continues || ((yes.falls || no.falls) && rest.continues) }

  /-- `switch (x.key)` over a union-typed local, one case per variant in order. -/
  partial def checkSwitch (T : Types) (s : Scope) (result : Ty) (e : Parse.Expr)
      (cases : List (Option Parse.Expr × List Parse.Stmt)) (span : Span) (rest : List Parse.Stmt) : Checked Block := do
    let .member (.var x _) key _ := e | unsupportedTy span "a switch other than on a union's tag field"
    let some (i, τ@(.union key' vs)) := s.lookup x | mismatch span s!"'{x}' is not a union"
    if key != key' then mismatch span s!"'{key}' is not the tag field of '{x}'"
    if protoName key then mismatch span s!"'{key}' is an Object.prototype property"
    let variants := Variants.toList vs
    if cases.length != variants.length then
      unsupportedTy span "a switch without exactly one case per variant (in the union's order)"
    let bodies ← (cases.zip variants).zipIdx.mapM fun (((label, body), (t, fs)), j) => do
      let ok := match label, t with
        | some (.literal (.string u) _), .str u' => u == u'
        | some (.literal (.boolean b) _), .bool b' => b == b'
        | _, _ => false
      if !ok then unsupportedTy span s!"case {j + 1} must be {tagLitTS t} (cases follow the union's order)"
      let σ := vrec' key t fs
      let n : Narrowed := { index := i, name := x, wide := τ, narrow := σ,
                            embed := injText j variants.length s!"{ident x}.2" }
      let b ← checkStmts T (s.narrow i σ) result body
      if j + 1 < variants.length && b.falls then
        unsupportedTy span s!"case {tagLitTS t} falls through to the next case"
      pure (b, n)
    let rest ← checkStmts T s result rest
    let casesTyped := bodies.foldr (fun (b, _) acc =>
      if acc.isEmpty then s!"(.one {b.typed})" else s!"(.cons {b.typed}\n  {acc})") ""
    let falls := (bodies.getLast?.map (·.1.falls)).getD false
    let breaks := bodies.any (·.1.breaks)
    let continues := bodies.any (·.1.continues)
    pure { typed := s!"(.switchU {s.varPath i} (by decide)\n  {casesTyped}\n  {rest.typed})",
           readable := fun ind k =>
             let kr := fun j => rest.readable j k
             switchArms x bodies { k with normal := kr, brk := kr } (ident x) ind,
           falls := (falls || breaks) && rest.falls, breaks := (falls || breaks) && rest.breaks,
           continues := continues || ((falls || breaks) && rest.continues) }
end

/-! ## Functions and files -/

structure CheckedFn where
  sig : FnSig
  body : Block

def checkFunction (T : Types) (fns : List FnSig) (f : Parse.Function) : Checked CheckedFn := do
  if fns.any (·.name == f.name) then
    throw { code := "A2004", message := s!"'{f.name}' is declared twice", span := f.span }
  let result ← T.resolve f.span 64 f.result
  let mut s : Scope := { fns, locals := [] }
  let mut params := []
  for p in f.params do
    let τ ← T.param p
    params := params ++ [(p.name, τ)]
    if s.locals.any (·.1 == p.name) || fns.any (·.name == p.name) || p.name == f.name then
      throw { code := "A2004", message := s!"'{p.name}' shadows a declaration in scope", span := p.span }
    s := { s with locals := s.locals ++ [(p.name, τ)] }
  let .block body _ := f.body | unsupportedTy f.span "this function body"
  let block ← checkStmts T s result body
  if block.falls then
    throw { code := "A2003", message := s!"'{f.name}' may finish without returning a value", span := f.span }
  if block.breaks || block.continues then
    throw { code := "A2003", message := "break or continue outside a loop or switch", span := f.span }
  pure { sig := { name := f.name, params, result }, body := block }

def checkProgram (p : Parse.Program) : Checked (Types × List CheckedFn) := do
  let T ← Types.ofProgram p
  let mut fns := []
  let mut out := []
  for f in p.functions do
    let c ← checkFunction T fns f
    fns := fns ++ [c.sig]
    out := out ++ [c]
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

  partial def printStmts (indent : String) (ss : List Stmt) : String :=
    if ss.isEmpty then "[]" else
      s!"[\n{indent}  " ++ s!",\n{indent}  ".intercalate (ss.map (printStmt (indent ++ "  "))) ++ "]"
end

def printFunction (fn : Function) : String :=
  "{ name := " ++ leanString fn.name ++ s!", params := {fn.params.map leanString}, body := " ++
    printStmts "    " fn.body ++ " }"

/-! ## The generated file -/

def sigName (f : String) : String := s!"sig.{ident f}"

/-- The Lean source for a checked file: the AST, the typed program, readable
definitions, and per-function source theorems. -/
def printFile (source namespace_ : String) (ast : Program) (T : Types) (fns : List CheckedFn) : String := Id.run do
  -- A line comment: a path may contain `/-`, which would open a block comment.
  let name := ((source.splitOn "/").getLast?.getD source).map fun c => if c == '\n' || c == '\r' then ' ' else c
  let mut out := s!"import V2.Proof.Adequacy\n\n-- Generated by ariadne2 from {name}. Do not edit.\n\n"
  out := out ++ s!"namespace {namespace_}\nopen V2\n\nset_option maxRecDepth 8192\nset_option linter.unusedVariables false\n\n"
  out := out ++ "/-- The source file in the model's syntax. -/\ndef ast : Program := [\n  " ++
    ",\n  ".intercalate (ast.map printFunction) ++ "]\n\n"
  for (n, τ) in T.named do
    out := out ++ s!"abbrev ty.{ident n} : Ty := {printTy τ}\n"
  if !T.named.isEmpty then out := out ++ "\n"
  for fn in fns do
    let s := fn.sig
    let ctx := "[" ++ ", ".intercalate (s.params.map fun (x, τ) => s!"({leanString x}, {T.print τ})") ++ "]"
    out := out ++ s!"def {sigName s.name} : Sig := " ++ "{ name := " ++ leanString s.name ++
      s!", params := {ctx}, result := {T.print s.result}, trivial := true " ++ "}\n"
  out := out ++ "\n"
  let nes := (fns.foldl (fun acc fn => acc ++ collectNe fn.body.typed) []).eraseDups
  for (a, b) in nes do
    out := out ++ s!"theorem ne.{ident a}.{ident b} : ({leanString a} : String) ≠ {leanString b} := by decide\n"
  if !nes.isEmpty then out := out ++ "\n"
  let mut earlier : List String := []
  for fn in fns do
    let s := fn.sig
    let φ := "[" ++ ", ".intercalate (earlier.map sigName) ++ "]"
    out := out ++ s!"def body.{ident s.name} : TStmts {φ} {sigName s.name}.params {sigName s.name}.result :=\n  " ++
      fn.body.typed ++ "\n\n"
    earlier := s.name :: earlier
  let all := "[" ++ ", ".intercalate (earlier.map sigName) ++ "]"
  let program := fns.foldl (fun acc fn => s!"(.cons {sigName fn.sig.name} body.{ident fn.sig.name} {acc})") ".nil"
  out := out ++ s!"abbrev sigs : Sigs := {all}\n\ndef typed : TProgram sigs :=\n  {program}\n\n"
  out := out ++ "theorem erased : typed.erase = ast := by kernel_rfl\n\ntheorem wf : typed.WF := by decide +kernel\n\n"
  out := out ++ "/-! ## Readable definitions -/\n\n"
  for fn in fns do
    let s := fn.sig
    let params := " ".intercalate (s.params.map fun (x, τ) => s!"({ident x} : {T.lean τ})")
    let dflt := s!"(Ty.default {T.print s.result})"
    out := out ++ s!"def {ident s.name} {params} : {T.lean s.result} :=\n  " ++
      fn.body.readable "  " ⟨fun _ => dflt, fun _ => dflt, fun _ => dflt⟩ ++ "\n\n"
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
    out := out ++ s!"def {ident s.name}.uncurried : {sigName s.name}.denote := fun xs => {applied}\n\n"
    out := out ++ s!"/-- Trivially safe: every input is in what the model covers. -/\n"
    out := out ++ s!"def {ident s.name}.safety : {sigName s.name}.params.denote → Bool := fun _ => true\n\n"
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
    out := out ++ s!"/-- Every run of `{s.name}` on arguments representing its inputs converges to a value\nrepresenting the readable definition's result. -/\n"
    out := out ++ s!"theorem {ident s.name}.source {binders} (vs : List JSValue)\n    (args : ArgsRep {sigName s.name}.params vs {tuple}) :\n"
    out := out ++ s!"    ∃ w, Converges (fun fuel' => run ast fuel' {leanString s.name} vs) (.ok w) ∧\n      Ty.Rep {T.print s.result} w ({call}) :=\n"
    out := out ++ s!"  source_of erased wf denote_eq safety_eq {fvar} {tuple} vs args rfl\n\n"
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
where
  fieldsJson (fs : Fields) : String :=
    "[" ++ ",".intercalate ((Fields.toList fs).map fun (f, τ) => "[" ++ leanString f ++ "," ++ tyJson τ ++ "]") ++ "]"

/-- Each function's name, whether it is exported, and its parameter and result types, as JSON lines. -/
def signatures (text : String) : Checked (List String) := do
  let parsed ← Parse.parse text
  let (_, fns) ← checkProgram parsed
  return (parsed.functions.zip fns).map fun (f, c) =>
    "{\"name\":" ++ leanString c.sig.name ++ ",\"exported\":" ++ toString f.exported ++ ",\"params\":[" ++
      ",".intercalate (c.sig.params.map (tyJson ·.2)) ++ "],\"result\":" ++ tyJson c.sig.result ++ "}"

/-- Parse, convert and check a TypeScript file, returning the generated Lean source. -/
def translate (source namespace_ text : String) : Checked String := do
  let parsed ← Parse.parse text
  let ast ← convertProgram parsed
  let (T, fns) ← checkProgram parsed
  pure (printFile source namespace_ ast T fns)

end V2.Front
