import Ariadne.Front.Convert
import Ariadne.Front.Emit
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

/-- `xs.f args` when the receiver is a name or a field path (its type is then known when it elaborates), else
`List.f args xs`. -/
def listCall (recv f : String) (args : List String := []) (last : Bool := true) : String :=
  let path := !recv.isEmpty && recv.all fun c => c.isAlphanum || c == '_' || c == '.' || c == '«' || c == '»' || c == '\''
  if path then " ".intercalate (s!"{recv}.{f}" :: args)
  else if last then " ".intercalate (s!"List.{f}" :: args ++ [recv]) else " ".intercalate (s!"List.{f}" :: recv :: args)

/-- Always quoted: names used for generated inequality witnesses. -/
def quoted (x : String) : String := s!"«{x}»"

/-- Lean's keywords, and the names that read as syntax: an identifier spelled as one stays quoted. -/
def leanKeywords : List String :=
  ["at", "by", "do", "else", "end", "fun", "have", "if", "import", "in", "let", "match", "mut", "namespace", "open",
   "section", "show", "then", "where", "with", "from", "for", "unless", "return", "break", "continue", "try", "catch",
   "finally", "this", "Type", "Sort", "Prop", "deriving", "instance", "structure", "inductive", "class", "theorem",
   "def", "abbrev", "example", "axiom", "universe", "variable", "macro", "syntax", "notation", "infix", "infixl",
   "infixr", "prefix", "postfix", "partial", "private", "protected", "noncomputable", "mutual", "calc", "suffices",
   "nomatch", "nofun", "local", "scoped", "attribute", "export", "set_option", "termination_by", "decreasing_by",
   "opaque", "extends", "using", "sorry", "admit", "forall", "exists", "matches", "fun", "omit", "include", "elab",
   "macro_rules", "unif_hint", "nonrec", "public", "meta", "module", "deprecated", "obtain", "rfl", "safety_spec"]

/-- A name as Lean reads it: bare when it is a plain identifier, else quoted (`«wrong-key»`, `«at»`). -/
def ident (x : String) : String :=
  let plain := match x.toList with
    | [] => false
    | c :: cs => (c.isAlpha || (c == '_' && !cs.isEmpty)) && cs.all fun d => d.isAlphanum || d == '_'
  if plain && !leanKeywords.contains x then x else quoted x

/-- Whether `text` mentions the variable `x`: `ident x` neither inside a longer name nor after a `.` (a field
of the same name). -/
def mentions (text x : String) : Bool :=
  let parts := text.splitOn (ident x)
  let nameChar (c : Char) := c.isAlphanum || c == '_' || c == '\'' || c == '!' || c == '?' || c == '«' || c == '»'
  (List.range (parts.length - 1)).any fun i =>
    let before := (parts[i]!.toList.getLast?).getD ' '
    let after := (parts[i + 1]!.toList.head?).getD ' '
    !nameChar before && before != '.' && !nameChar after

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

def Variants.toList : Variants → List (TagLit × Fields)
  | .one t fs => [(t, fs)]
  | .cons t fs rest => (t, fs) :: Variants.toList rest

/-! ### Structures and inductives

Readable definitions use the program's own types (`Ty.den` with the generated `names`): a named record
whose fields can name a structure's is that structure, a named union whose tags can name an inductive's
constructors is that inductive, and a record whose first field is a tag (a union's variant) is its payload,
the fields after the tag. Other types are the products, sums and lists they denote. -/

/-- The names Lean derives for a structure or an inductive, which its fields and constructors cannot take. -/
def derivedNames : List String :=
  ["mk", "rec", "casesOn", "recOn", "noConfusion", "noConfusionType", "below", "brecOn", "binductionOn", "ibelow",
   "ctorIdx", "toCtorIdx", "ctorElim", "ctorElimType", "induct", "inj", "injEq", "sizeOf_spec", "ext", "ext_iff"]

/-- Whether `f` can name a structure's field or an inductive's constructor. -/
def memberName (f : String) : Bool :=
  !derivedNames.contains f && match f.toList with
    | c :: _ => !c.isDigit
    | [] => false

/-- The fields after the tag of a record whose first field is a tag. -/
def tagged? : Ty → Option Fields
  | .record (.cons _ (.tag _) fs) => some fs
  | _ => none

/-- The structure a named record (other than a variant) is. -/
def Types.structName? (T : Types) (τ : Ty) : Option String :=
  match τ with
  | .record fs => if (tagged? τ).isNone && (Fields.toList fs).all (memberName ·.1) then (T.nameOf? τ).map ident else none
  | _ => none

/-- The inductive a union is, with its constructors (`«U».«tag»`): the first named union with its variants
whose tags can all name constructors. -/
def Types.inductive? (T : Types) : Ty → Option (String × List String)
  | .union _ vs => T.named.findSome? fun ((n : String), (σ : Ty)) => match σ with
    | .union _ vs' =>
      if vs' == vs && T.readable.contains n then
        let tags : Option (List String) := (Variants.toList vs).mapM fun (p : TagLit × Fields) =>
          (tagName p.1).filter memberName
        tags.map fun tags => (ident n, tags.map fun tn => s!"{ident n}.{ident tn}")
      else none
    | _ => none
  | _ => none

/-- The constructors' names of a union declared as an inductive. -/
def Types.ctorNames? (T : Types) (τ : Ty) : Option (List String) := (T.inductive? τ).map (·.2)

/-- The payload structure of a named union's variant `i` with more than one field, `«U».Variant.«tag»`. -/
def Types.payloadName? (T : Types) (τ : Ty) (i : Nat) : Option String := do
  let .union _ vs := τ | none
  let n ← T.nameOf? τ
  let (t, fs) ← (Variants.toList vs)[i]?
  if (Fields.toList fs).length < 2 then none
  let tn ← tagName t
  return s!"{ident n}.Variant.{ident tn}"

/-- The union (and variant index) a variant record `{key: tag, …fields}` belongs to, among the named types. -/
def Types.variantOf? (T : Types) (σ : Ty) : Option (Ty × Nat) :=
  T.named.findSome? fun (_, τ) => match τ with
    | .union key vs =>
      (Variants.toList vs).zipIdx.findSome? fun ((t, fs), i) =>
        if Ty.record (.cons key (.tag t) fs) == σ then some (τ, i) else none
    | _ => none

/-- How a value of a record whose first field is a tag is written: by its payload, the fields after the tag. -/
inductive Rep where
  /-- No fields: `()`. -/
  | unit
  /-- One field: its value. -/
  | single (τ : Ty)
  /-- A structure of the fields: the record's own (when it is named) or its union's `«U».Variant.«tag»`. -/
  | struct (name : String) (fields : List (String × Ty))
  /-- The fields' product. -/
  | tuple (fields : List (String × Ty))
  deriving Inhabited, BEq

/-- How a record whose first field is a tag is written. -/
def Types.rep (T : Types) (σ : Ty) : Option Rep := do
  let fs ← tagged? σ
  let fields := Fields.toList fs
  let free := fields.all (memberName ·.1)
  if let some n := (if !fields.isEmpty && free then T.nameOf? σ else none) then return .struct (ident n) fields
  match fields with
  | [] => return .unit
  | [(_, τ)] => return .single τ
  | _ =>
    match (T.variantOf? σ).bind fun (u, i) => T.payloadName? u i with
    | some V => return if free then .struct V fields else .tuple fields
    | none => return .tuple fields

/-- A value of a record whose first field is a tag, as its payload's text (atomic). -/
structure Payload where
  rep : Rep
  text : String
  deriving Inhabited

/-- The payload's fields as a tuple (`Fields.den`), as a union other than an inductive holds it. -/
def Payload.whole (p : Payload) : String :=
  match p.rep with
  | .unit => "()"
  | .single _ => s!"({p.text}, ())"
  | .struct _ fs => "(" ++ ", ".intercalate (fs.map (fun (f, _) => s!"{p.text}.{ident f}") ++ ["()"]) ++ ")"
  | .tuple _ => p.text

/-- The payload from its fields' tuple `e` (atomic). -/
def Rep.ofWhole (r : Rep) (e : String) : String :=
  match r with
  | .unit => "()"
  | .single _ => s!"{e}.1"
  | .struct n fs => "(" ++ " ".intercalate (s!"{n}.mk" :: (List.range fs.length).map fun k =>
      e ++ String.join (List.replicate k ".2") ++ ".1") ++ ")"
  | .tuple _ => e

mutual
  /-- The Lean type of a value of type `τ` (`Ty.den` with the generated `names`). -/
  partial def Types.lean (T : Types) (τ : Ty) : String :=
    match τ, T.rep τ with
    | _, some .unit => "Unit"
    | _, some (.single σ) => T.lean σ
    | _, some (.struct n _) => n
    | _, some (.tuple fs) => T.product fs
    | .bool, none => "Bool" | .int, none => "Int" | .number, none => "Int" | .string, none => "JSString"
    | _, none => match T.inductive? τ with
      | some (n, _) => n
      | none => match T.nameOf? τ with
        | some n => ident n
        | none => T.leanBody τ

  /-- `Types.lean`, other than by the type's name: the product, sum, list or option it denotes. -/
  partial def Types.leanBody (T : Types) : Ty → String
    | .bool => "Bool" | .int => "Int" | .number => "Int" | .string => "JSString"
    | .tag _ => "Unit"
    | .lits _ as => s!"Fin {as.length + 1}"
    | .option _ σ => s!"Option {atomText (T.lean σ)}"
    | .array σ => s!"List {atomText (T.lean σ)}"
    | .map σ => s!"List (JSString × {T.lean σ})"
    | .record fs => T.product (Fields.toList fs)
    | .union _ vs => " ⊕ ".intercalate ((Variants.toList vs).map fun (_, fs) => atomText (T.product (Fields.toList fs)))

  /-- `A × B × Unit`: the product of the fields' types. -/
  partial def Types.product (T : Types) (fs : List (String × Ty)) : String :=
    fs.foldr (fun (_, σ) acc => s!"{atomText (T.lean σ)} × {acc}") "Unit"
end

def Fields.ofList : List (String × Ty) → Fields
  | [] => .nil
  | (f, τ) :: rest => .cons f τ (Fields.ofList rest)

def Variants.ofList : List (TagLit × Fields) → Option Variants
  | [] => none
  | [(t, fs)] => some (.one t fs)
  | (t, fs) :: rest => (Variants.ofList rest).map (.cons t fs)

/-! ## The checking monad

Checking is `Except Diagnostic`, with a log on the side: what each checked expression, declaration and
function denotes, for editors (the playground's hovers). The log never affects the result. -/

/-- One logged fact: the type of the expression, variable or function at `span`, and for an expression
the readable Lean term it denotes and, when it is not trivially safe, its safety condition. -/
structure Hover where
  span : Span
  kind : String
  name : String := ""
  ty : Ty
  term : String := ""
  safe : String := ""
  /-- For a function: its parameters' names and types. -/
  params : List (String × Ty) := []
  deriving Inhabited

structure CheckLog where
  hovers : Array Hover := #[]
  inequalities : List (String × String) := []
  /-- Loops checked so far, to name their bodies. -/
  loops : Nat := 0
  /-- The named types, once resolved, to print the logged types with. -/
  types : Option Types := none

abbrev CheckM := ExceptT Diagnostic (StateM CheckLog)

def logHover (h : Hover) : CheckM Unit := modify fun l => { l with hovers := l.hovers.push h }

/-- A new loop's number. -/
def nextLoop : CheckM Nat := modifyGet fun l => (l.loops, { l with loops := l.loops + 1 })

def mismatch (span : Span) (message : String) : CheckM α :=
  throw { code := "A2002", message, span }

def unsupportedTy (span : Span) (what : String) : CheckM α :=
  throw { code := "A1001", message := s!"{what} is outside the supported subset", span }

mutual
  /-- Union members, with aliases of unions expanded. -/
  partial def Types.members (T : Types) (span : Span) (fuel : Nat) : Parse.Ty → CheckM (List Parse.Ty)
    | .union a b => return (← T.members span fuel a) ++ (← T.members span fuel b)
    | .fieldReadonly t => T.members span fuel t
    | t@(.named n) => match fuel, T.aliases.lookup n with
      | f + 1, some def_@(.union ..) => T.members span f def_
      | _, _ => pure [t]
    | t => pure [t]

  partial def Types.resolve (T : Types) (span : Span) (fuel : Nat) (t : Parse.Ty) : CheckM Ty := do
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

  partial def Types.single (T : Types) (span : Span) (fuel : Nat) : Parse.Ty → CheckM Ty
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
  partial def Types.recordUnion (T : Types) (span : Span) (fuel : Nat) (ms : List Parse.Ty) : CheckM Ty := do
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

def Types.ofProgram (p : Parse.Program) : CheckM Types := do
  let mut T : Types := { aliases := p.aliases }
  for (n, t) in p.aliases do
    let τ ← T.resolve {} 64 t
    T := { T with named := T.named ++ [(n, τ)] }
  return T

def Types.param (T : Types) (p : Parse.Param) : CheckM Ty := T.resolve p.span 64 p.ty

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

structure Scope where
  /-- Variables a `switch` narrowed to a variant, with how the variant is written (`Rep`). -/
  payloads : List (String × Rep) := []
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
  | y :: ys => s!"(.there ne.{quoted x}.{quoted y} {varPathN x ys})"

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

def Scope.varPath (s : Scope) (i : Nat) : CheckM String := do
  let x := s.locals[i]!.1
  let skipped := (s.locals.take i).map (·.1)
  modify fun l => { l with inequalities := l.inequalities ++ skipped.map (x, ·) }
  return varPathN x skipped

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

/-- A safety expression composed with a statement tree. -/
def andCode (a : String) (b : Code) : Code :=
  if a == "true" then b else c!"{paren a} && ({b})"

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
def Narrowed.wrap (n : Narrowed) (k : String → Code) : String → Code :=
  fun i =>
    let rest := k i
    if n.embed != ident n.name && mentions rest.preview n.name then
      Code.binding (ident n.name) "" (.text n.embed) rest i
    else rest

def vrec' (key : String) (t : TagLit) (fs : Fields) : Ty := .record (.cons key (.tag t) fs)

/-- Readable `this` with field `j` (of `n`) replaced. -/
def tupleSetText (e : String) (j n : Nat) (v : String) : String :=
  let before := (List.range j).map (projText e)
  let _ := n
  "(" ++ ", ".intercalate (before ++ [v, e ++ String.join (List.replicate (j + 1) ".2")]) ++ ")"

/-- Readable read of field `k` of a value `e` (atomic) of record type `τ`: by name when the record has one
(a variant's tag, field 0, is `()`). -/
def Types.fieldText (T : Types) (τ : Ty) (e : String) (k : Nat) : String :=
  match T.rep τ, τ with
  | some r, _ => if k == 0 then "()" else match r with
    | .unit => "()"
    | .single _ => e
    | .struct _ fs => s!"{e}.{ident fs[k - 1]!.1}"
    | .tuple _ => projText e (k - 1)
  | none, .record fs => if (T.nameOf? τ).isSome then s!"{e}.{ident (Fields.toList fs)[k]!.1}" else projText e k
  | none, _ => projText e k

/-- Readable `e` (atomic) of record type `τ` with field `k` set to `v`. -/
def Types.setText (T : Types) (τ : Ty) (e : String) (k : Nat) (v : String) : String :=
  match T.rep τ, τ with
  | some r, _ => if k == 0 then e else match r with
    | .unit => e
    | .single _ => v
    | .struct _ fs => s!"\{ {e} with {ident fs[k - 1]!.1} := {v} }"
    | .tuple fs => tupleSetText e (k - 1) fs.length v
  | none, .record fs => match T.structName? τ with
    | some _ => s!"\{ {e} with {ident (Fields.toList fs)[k]!.1} := {v} }"
    | none => tupleSetText e k (Fields.toList fs).length v
  | none, _ => tupleSetText e k 0 v

/-- Readable injection of variant `i` of the union `τ`, given by its payload. -/
def Types.injectText (T : Types) (τ : Ty) (i : Nat) (p : Payload) : String :=
  match (T.ctorNames? τ).bind (·[i]?), τ with
  | some c, _ => if p.rep == .unit then c else s!"({c} {atomText p.text})"
  | none, .union _ vs => injText i (Variants.toList vs).length p.whole
  | none, _ => p.whole

/-- A value `e` (atomic) of a record whose first field is a tag, as a payload. -/
def Types.payload (T : Types) (σ : Ty) (e : String) : Payload :=
  let rep := (T.rep σ).getD .unit
  { rep, text := if rep == .unit then "()" else e }

/-- Use a value of type `out.ty` at type `τ`: equal, or a no-op embedding. -/
def coerce (T : Types) (span : Span) (out : Out) (τ : Ty) : CheckM Out := do
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
      let (t, fs) := variants[i]!
      let p := T.payload (vrec' key t fs) out.term
      return { ty := τ, typed := s!"(.widen (.variant {vidxPath i variants.length}) {out.typed})",
               readable := T.injectText τ i p, atomic := true, trivial := out.trivial, safe := out.safe }
    | none => mismatch span s!"{out.ty.ts} where {τ.ts} is expected"
  | _ => mismatch span s!"{out.ty.ts} where {τ.ts} is expected"

def nullTestVar : Parse.Expr → Option (String × Bool)
  | .binary "==" (.var x _) (.literal .null _) _ => some (x, true)
  | .binary "!=" (.var x _) (.literal .null _) _ => some (x, false)
  | _ => none

/-- The narrowing a `x == null` / `x != null` test establishes on an optional local. -/
def Scope.nullNarrowing (s : Scope) (span : Span) (x : String) : CheckM (Narrowed × String) := do
  match s.lookup x with
  | some (i, τ@(.option _ σ)) =>
    if !σ.nonNullish then mismatch span "a nested optional"
    return ({ index := i, name := x, wide := τ, narrow := σ, embed := s!"some {ident x}" }, ← s.varPath i)
  | some _ => mismatch span s!"'{x}' is not optional"
  | none => throw { code := "A2001", message := s!"unknown variable '{x}'", span }

def protoName (f : String) : Bool := protoNames.contains f

def declare (s : Scope) (span : Span) (x : String) (τ : Ty) : CheckM Scope := do
  if x == "this" || s.locals.any (·.1 == x) || s.fns.any (fun f => f.name == x && !f.method) then
    throw { code := "A2004", message := s!"'{x}' shadows a declaration in scope", span,
            help := some "Rename it: the model requires names in scope to be distinct." }
  logHover { span, kind := "var", name := x, ty := τ }
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
def Scope.fnRef (s : Scope) (span : Span) (f : String) : CheckM (String × FnSig) := do
  if s.locals.any (·.1 == f) then mismatch span s!"'{f}' is a local, not a declared function"
  let some j := s.fns.findIdx? (fun g => g.name == f && !g.method)
    | throw { code := "A2001", message := s!"'{f}' is not a function declared earlier", span }
  return (fnPath (s.fns.length - 1 - j), s.fns[j]!)

/-- The state (`this`) of the method being checked: its path, record fields, and
the field `f` (a map) with its index and value type. -/
def Scope.stateField (s : Scope) (span : Span) (f : String) : CheckM (String × Fields × Nat × Ty) := do
  let some (i, .record fs) := s.lookup "this" | mismatch span "'this' outside a method"
  let fields := Fields.toList fs
  let some j := fields.findIdx? (·.1 == f) | mismatch span s!"no field '{f}'"
  let .map τ := fields[j]!.2 | mismatch span s!"field '{f}' is not a Map"
  return (← s.varPath i, fs, j, τ)

/-- A method of the class, by name: its `FVar` path and signature. -/
def Scope.methodRef (s : Scope) (span : Span) (m : String) : CheckM (String × FnSig) := do
  let some j := s.fns.findIdx? (fun g => g.name == m && g.method)
    | throw { code := "A2001", message := s!"'{m}' is not a method declared earlier (or it calls itself)", span }
  return (fnPath (s.fns.length - 1 - j), s.fns[j]!)

mutual
  partial def checkExpr (T : Types) (s : Scope) (e : Parse.Expr) (expected : Option Ty) : CheckM Out := do
    let out ← inferExpr T s e expected
    match expected with
    | some τ => coerce T e.span out τ
    | none => pure out

  /-- `inferExprCore`, logging what the expression denotes. -/
  partial def inferExpr (T : Types) (s : Scope) (e : Parse.Expr) (expected : Option Ty) : CheckM Out := do
    let out ← inferExprCore T s e expected
    logHover { span := e.span, kind := "expr", ty := out.ty, term := out.readable,
               safe := if out.trivial then "" else out.safe }
    return out

  partial def inferExprCore (T : Types) (s : Scope) (e : Parse.Expr) (expected : Option Ty) : CheckM Out := do
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
      | some (i, τ) =>
        -- A variable narrowed to a variant without fields is not bound: its value is `()`.
        let readable := if s.payloads.lookup x == some .unit then "()" else ident x
        return { ty := τ, typed := s!"(.var {← s.varPath i})", readable, atomic := true }
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
      | "++", .int | "--", .int =>
        let sym := if op == "++" then "+" else "-"
        return { ty := .int, typed := s!"(.iinc {op == "++"} {a.typed})", readable := s!"{a.term} {sym} 1",
                 trivial := a.trivial, safe := a.safe }
      | "++", .number | "--", .number =>
        let sym := if op == "++" then "+" else "-"
        return { ty := .number, typed := s!"(.ninc {op == "++"} {a.typed})", readable := s!"{a.term} {sym} 1",
                 trivial := false, safe := andText a.ok s!"Ariadne.inRange ({a.term} {sym} 1)" }
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
               readable := s!"({listCall (T.fieldText (.record fsT) (ident "this") j) "length"} : Int)", atomic := true }
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
      return { ty := sig.result, typed := s!"(.callThis {fpath} {← s.varPath i} {typedArgs})",
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
    | .call (.member (.var "Math" _) "floor" _) [.binary "/" a b _] _ => do
      let a ← checkExpr T s a (some .number)
      let b ← checkExpr T s b (some .number)
      return { ty := .number, typed := s!"(.bin .ndiv {a.typed} {b.typed})", readable := s!"Int.fdiv {a.term} {b.term}",
               trivial := false,
               safe := andText (both a b) s!"{b.term} != 0 && Ariadne.inRange {a.term} && Ariadne.inRange {b.term}" }
    | .call (.member recv m _) args span => checkMethod T s recv m args span expected
    | .member a f span => do
      let a ← inferExpr T s a none
      match a.ty, f with
      | .array _, "length" | .string, "length" =>
        return { ty := .number, typed := s!"(.{if a.ty == .string then "slength" else "length"} {a.typed})",
                 readable := s!"({listCall a.term "length"} : Int)", atomic := true, trivial := a.trivial, safe := a.safe }
      | .record fs, _ =>
        let fields := Fields.toList fs
        match fields.findIdx? (·.1 == f) with
        | some k =>
          if protoName f then mismatch span s!"'{f}' is an Object.prototype property"
          let readable := T.fieldText a.ty a.term k
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
          return (true, ({ ty := .array τ, typed := "", readable := listCall (T.fieldText (.record fsT) (ident "this") j) "map" ["Prod.fst"] } : Out),
            s!"spreadKeys {path} {fidxPath j}")
        | .spread (.call (.member (.member (.var "this" _) f _) "values" _) [] _) sp => do
          let (path, fsT, j, σ) ← s.stateField sp f
          if τ != σ then mismatch sp s!"map values ({σ.ts}) where {τ.ts} is expected"
          return (true, ({ ty := .array τ, typed := "", readable := listCall (T.fieldText (.record fsT) (ident "this") j) "map" ["Prod.snd"] } : Out),
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
      (expected : Option Ty) : CheckM (Out × Out) := do
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
      (span : Span) (expected : Option Ty) : CheckM Out := do
    let a ← inferExpr T s recv none
    if a.ty == .string then
      match m, args with
      | "startsWith", [t] | "endsWith", [t] | "includes", [t] | "indexOf", [t] =>
        let t ← checkExpr T s t (some .string)
        let (ty, fn) : Ty × String := match m with
          | "startsWith" => (.bool, "Ariadne.strStartsWith")
          | "endsWith" => (.bool, "Ariadne.strEndsWith")
          | "includes" => (.bool, "Ariadne.strIncludes")
          | _ => (.number, "Ariadne.strIndexOf")
        return { ty, typed := s!"(.smethod .{m} {a.typed} {t.typed})", readable := s!"{fn} {a.term} {t.term}",
                 trivial := a.trivial && t.trivial, safe := both a t }
      | "slice", [i] =>
        let i ← checkExpr T s i (some .number)
        return { ty := .string, typed := s!"(.slice1 {a.typed} {i.typed})",
                 readable := s!"Ariadne.strSlice {a.term} {i.term} ({listCall a.term "length"} : Int)",
                 trivial := a.trivial && i.trivial, safe := both a i }
      | "slice", [i, j] =>
        let i ← checkExpr T s i (some .number)
        let j ← checkExpr T s j (some .number)
        return { ty := .string, typed := s!"(.slice2 {a.typed} {i.typed} {j.typed})",
                 readable := s!"Ariadne.strSlice {a.term} {i.term} {j.term}",
                 trivial := a.trivial && i.trivial && j.trivial,
                 safe := andTText a.trivial a.safe (i.trivial && j.trivial) (both i j) }
      | _, _ => unsupportedTy span s!"the string method '{m}' with these arguments"
    let .array τ := a.ty | unsupportedTy span s!"the method '{m}' of {a.ty.ts}"
    let [arg] := args | unsupportedTy span s!"'{m}' with other than one argument"
    match m with
    | "includes" =>
      if !τ.prim then mismatch span s!"'includes' on an array of {τ.ts} (objects compare by identity)"
      let x ← checkExpr T s arg (some τ)
      return { ty := .bool, typed := s!"(.includes (by decide +kernel) {a.typed} {x.typed})",
               readable := listCall a.term "any" [s!"(· == {x.term})"] false, trivial := a.trivial && x.trivial,
               safe := both a x }
    | "some" | "every" | "find" | "filter" | "map" => do
      let result := if m == "map" then (match expected with | some (.array σ) => some σ | _ => none) else some .bool
      let f ← checkFn T s span arg τ result
      let (ctor, ty, readable, cond) := match m with
        | "some" => ("any", Ty.bool, listCall a.term "any" [f.lam] false, s!"Ariadne.anySafe {f.lam} {f.lamSafe} {a.term}")
        | "every" => ("all", .bool, listCall a.term "all" [f.lam] false, s!"Ariadne.allSafe {f.lam} {f.lamSafe} {a.term}")
        | "find" => ("find", .option .undef τ, listCall a.term "find?" [f.lam],
          s!"Ariadne.anySafe {f.lam} {f.lamSafe} {a.term}")
        | "filter" => ("filter", .array τ, listCall a.term "filter" [f.lam], listCall a.term "all" [f.lamSafe] false)
        | _ => ("map", .array f.ty, listCall a.term "map" [f.lam], listCall a.term "all" [f.lamSafe] false)
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
      CheckM Fn := do
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
  partial def checkCmp (T : Types) (s : Scope) (span : Span) (arg : Parse.Expr) (τ : Ty) : CheckM Fn := do
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
      (_expected : Option Ty) : CheckM Out := do
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
      -- Division and remainder: the divisor must not be zero (a `RangeError` or `NaN`).
      | "/", .int => pure { mk .int "idiv" s!"Int.tdiv {a.term} {b.term}" with
          trivial := false, safe := andText (both a b) s!"{b.term} != 0" }
      | "%", .int => pure { mk .int "imod" s!"Int.tmod {a.term} {b.term}" with
          trivial := false, safe := andText (both a b) s!"{b.term} != 0" }
      | "%", .number => pure { mk .number "nmod" s!"Int.tmod {a.term} {b.term}" with
          trivial := false, safe := andText (both a b) s!"{b.term} != 0 && Ariadne.inRange (Int.tmod {a.term} {b.term})" }
      | "/", .number => mismatch span "'/' on numbers gives fractions (use Math.floor(a / b))"
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
      Ty → CheckM Out
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
            | none => (s!"(.keep (by decide +kernel) {accU})",
                (if (T.rep τ).isSome then projText "r'" (k - 1) else projText "r'" k) :: accR)) (".nil", [])
        let (esT, esS) := foldSafe (src.map (·.2))
        -- A structure's `{ ...r, f: v }` is `{ r with f := v }`; a variant's tag stays as it is.
        let updates := src.filterMap fun (f, o) => match fields.findIdx? (·.1 == f) with
          | some k => if (T.rep τ).isSome && k == 0 then none else some (f, o.readable)
          | none => none
        let withText := if updates.isEmpty then r.readable else
          s!"\{ {r.term} with {", ".intercalate (updates.map fun (f, v) => s!"{ident f} := {v}")} }"
        let text := match T.rep τ, T.structName? τ with
          | some (.struct ..), _ | none, some _ => withText
          | some .unit, _ => r.readable
          | some (.single _), _ => (updates.head?.map (·.2)).getD r.readable
          | some (.tuple _), _ => s!"let r' := {r.readable}; ({", ".intercalate (readable.drop 1 ++ ["()"])})"
          | none, none => s!"let r' := {r.readable}; ({", ".intercalate (readable ++ ["()"])})"
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
        let mk (n : String) (terms : List String) : String :=
          if terms.isEmpty then s!"{n}.mk" else s!"({" ".intercalate (s!"{n}.mk" :: terms)})"
        let tuple (terms : List String) : String := "(" ++ ", ".intercalate (terms ++ ["()"]) ++ ")"
        -- A variant is its payload: the fields after the tag.
        let readable := match T.rep τ, T.structName? τ with
          | some .unit, _ => "()"
          | some (.single _), _ => (sel.2[1]?).getD "()"
          | some (.struct n _), _ => mk n (sel.2.drop 1)
          | some (.tuple _), _ => tuple (sel.2.drop 1)
          | none, some n => mk n sel.2
          | none, none => tuple sel.2
        return { ty := τ, typed := s!"(.record {typedEntries} {sel.1} (by decide +kernel))",
                 readable, atomic := true, trivial := esT, safe := esS }
    | τ@(.option _ σ) => do
      let r ← checkRecord T s entries span σ
      coerce T span r τ
    | τ => mismatch span s!"an object literal where {τ.ts} is expected"
end

/-! ## Statements -/

/-- Readable continuations, rendered at the indentation where they are placed. -/
structure KText where
  normal : String → Code
  brk : String → Code
  cont : String → Code

def KText.wrap (k : KText) (n : Narrowed) : KText := ⟨n.wrap k.normal, n.wrap k.brk, n.wrap k.cont⟩

/-- A checked statement list: typed syntax, readable printers of its denotation and
of its safety condition (each taking the continuations' text), and how it can end. -/
structure Block where
  typed : String
  readable : (indent : String) → KText → Code
  safe : (indent : String) → KText → Code
  trivial : Bool
  falls : Bool
  breaks : Bool
  continues : Bool
  /-- The variables of the scope the statements may assign (`TStmts.writes`). -/
  writes : List String := []
  /-- No `return`, no `break` of its own, no `continue` of its own (`TStmts.noRet`, `noBrk`, `noCont`). -/
  noRet : Bool := true
  noBrk : Bool := true
  noCont : Bool := true

/-- Always completes normally (`TStmts.closed`). -/
def Block.closed (b : Block) : Bool := b.noRet && b.noBrk && b.noCont

def _root_.List.unite (a b : List String) : List String := a ++ b.filter (!a.contains ·)

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

/-- A variable's value in an environment tuple (a variable narrowed to a variant without fields is not bound). -/
def Scope.valueText (s : Scope) (x : String) : String :=
  if s.payloads.lookup x == some .unit then "()" else ident x

/-- The variables of the scope a statement assigns, in the scope's order (`Ctx.sub`). -/
def Scope.stateVars (s : Scope) (ws : List String) : List String := (s.locals.filter (ws.contains ·.1)).map (·.1)

/-- A state: the assigned variables as a flat tuple (`Ctx.tup`), as a term or a pattern. -/
def Scope.stateText (s : Scope) (ws : List String) : String :=
  match s.stateVars ws with
  | [] => "()"
  | [x] => s.valueText x
  | xs => "(" ++ ", ".intercalate (xs.map s.valueText) ++ ")"

/-- The value of an `if`, null test or `switch` whose branches are closed: `let state := branches; rest`. -/
def branchValueText (s : Scope) (ws : List String) (branches : String → KText → Code) (rest : Code) (i : String) :
    Code :=
  let st := s.stateText ws
  let kv : KText := ⟨fun _ => st, fun _ => st, fun _ => st⟩
  let j := i ++ "  "
  if rest.preview == st then branches i kv
  else Code.binding st "" (c!"\n{j}{branches j kv}") rest i

/-- The join point after branches assigning `ws` (`Ctx.join`): `let after := fun state => rest`, the branches
going on with `after state`. It is bound before the branches, so `rest` sees the variables as they were
before any narrowing. -/
def joinText (s : Scope) (ws : List String) (rest : Code) (branches : Code → Code) (i : String) : Code :=
  let after := s!"after{i.length}'"
  let st := s.stateText ws
  c!"let {after} := fun {st} =>\n{i}  {rest}\n{i}{branches c!"{after} {st}"}"

/-- The safety condition after branches that narrow `x`: the rest in each branch, unless it reads `x` (the
join point then gives it `x` as it was before the branches). -/
def narrowedJoinText (s : Scope) (x : String) (ws : List String) (rest : String → Code)
    (branches : (String → Code) → Code) (i : String) : Code :=
  let text := rest (i ++ "  ")
  if mentions text.preview x then joinText s ws text (fun call => branches fun _ => call) i else branches rest

/-- Readable `switch`: a match on the inductive's constructors (or nested matches on the union's sum), one
leaf per variant; a narrowed variable is bound to its variant's payload. -/
def switchLeaves (render : Block → String → KText → Code) (x : String) (ctors : Option (List String))
    (reps : List Rep) (leaves : List Leaf) (k : KText) (scrut ind : String) : Code :=
  -- A narrowed leaf in a sum binds the payload's fields as a tuple: a structure is built from them.
  -- `inSum`: the leaf's pattern is in a sum (it binds the fields' tuple, or for one field the field);
  -- `whole`: there is no pattern (`x` is the fields' tuple). A structure is then built from the fields.
  let leafText (l : Leaf) (r : Rep) (inSum whole : Bool) (j : String) : Code := match l with
    | .narrowed b n =>
      let body := render b j (k.wrap n)
      let build := match r with
        | .struct .. => inSum || whole
        | .single _ => whole
        | _ => false
      if build && mentions body.preview x then c!"let {ident x} := {r.ofWhole (ident x)}\n{j}{body}" else body
    | .run b => render b j k
    | .normal => k.normal j
  -- What a leaf's pattern binds: the narrowed variable's payload (in a sum, its fields' tuple), else nothing.
  let bind (l : Leaf) (r : Rep) (inSum : Bool) : String := match l, r with
    | .narrowed .., .unit => "_"
    | .narrowed .., .single _ => if inSum then s!"({ident x}, ())" else ident x
    | .narrowed .., _ => ident x
    | _, _ => "_"
  let j := ind ++ "  "
  match ctors, leaves with
  | some cs, _ =>
    let arms := (cs.zip (reps.zip leaves)).map fun (c, (r, l)) =>
      c!"{ind}| {if r == .unit then c else s!"{c} {bind l r false}"} =>\n{j}{leafText l r false false j}"
    c!"match {scrut} with\n" ++ Code.intercalate "\n" arms
  | none, [l] => leafText l reps[0]! false true ind
  | none, _ =>
    let rec nested (ls : List (Leaf × Rep)) (scrut ind : String) : Code :=
      let j := ind ++ "  "
      match ls with
      | [] => ""
      | [(l, r)] => leafText l r true false ind
      | (l, r) :: [(l', r')] =>
        c!"match {scrut} with\n{ind}| Sum.inl {bind l r true} =>\n{j}{leafText l r true false j}\n" ++
          c!"{ind}| Sum.inr {bind l' r' true} =>\n{j}{leafText l' r' true false j}"
      | (l, r) :: more =>
        c!"match {scrut} with\n{ind}| Sum.inl {bind l r true} =>\n{j}{leafText l r true false j}\n" ++
          c!"{ind}| Sum.inr p' =>\n{j}{nested more "p'" j}"
    nested (leaves.zip reps) scrut ind

/-- `if (c) yes else no; rest`, rendered for the denotation or the safety condition.
When both branches may complete, the rest is bound once as a join point instead of
being repeated in each branch. -/
def iteText (render : Block → String → KText → Code) (idiom : Bool) (s : Scope) (c : String)
    (yes no rest : Block) (i : String) (k : KText) : Code :=
  let j := i ++ "  "
  if idiom && yes.closed && no.closed then
    branchValueText s (yes.writes.unite no.writes) (fun j kv =>
      let j' := j ++ "  "
      c!"if {c} then\n{j'}{render yes j' kv}\n{j}else\n{j'}{render no j' kv}") (render rest i k) i
  else
  if yes.falls && no.falls && rest.typed != ".nil" then
    joinText s (yes.writes.unite no.writes) (render rest j k) (fun call =>
      let k' := { k with normal := fun _ => call }
      c!"if {c} then\n{j}{render yes j k'}\n{i}else\n{j}{render no j k'}") i
  else
    let k' := { k with normal := fun j' => render rest j' k }
    c!"if {c} then\n{j}{render yes j k'}\n{i}else\n{j}{render no j k'}"

/-- The Lean type of a variable's readable value. -/
def Scope.varTypeText (s : Scope) (T : Types) (x : String) : String :=
  T.lean (((s.lookup x).map (·.2)).getD .bool)

/-- A hoisted declaration with a structural reference. No markers are embedded in text. -/
def namedBody (s : Scope) (T : Types) (id : Nat) (state : List String)
    (ty lam : String) (body : Code) (implicit : String := "") : Code :=
  let captured := (s.locals.reverse.filter fun (x, _) =>
    !state.contains x && mentions body.preview x && s.payloads.lookup x != some .unit).map (·.1)
  let params := String.join (captured.map fun x => s!" ({ident x} : {s.varTypeText T x})")
  .hoisted id (implicit ++ params) ty (" ".intercalate (captured.map ident)) c!"{lam} =>\n    {body}"

/-- A loop: `Ariadne.forIn items (fun binder next exit state => body) (fun state => rest) state`, or, when its
body is direct, `let state := Ariadne.fold state items (fun state binder => body); rest`. The readable
definition's state, like the safety condition's (`TStmts.safeR`), is the variables the body assigns; the safety
condition keeps every loop as `Ariadne.forIn`. -/
def loopText (render : Block → String → KText → Code) (s : Scope) (items binder : String)
    (pre : String → String)
    (body rest : Block) (idiom : Bool) (i : String) (k : KText) (T : Types) (id : Nat) (binderTy resultTy : String) :
    Code :=
  let d := i.length
  let (nx, ex) := (s!"next{d}'", s!"exit{d}'")
  let j := i ++ "  "
  -- The state: the variables the body assigns (`TStmts.denoteR`), and its type.
  let st := s.stateText body.writes
  let vars := s.stateVars body.writes
  let stTy := if vars.isEmpty then "Unit" else " × ".intercalate (vars.map fun x => s.varTypeText T x)
  let jd := "    "
  -- A body with no `return` and no `break` of its own (`TStmts.direct`): a fold, the body ending with the
  -- state.
  if idiom && body.noRet && body.noBrk then
    let kd : KText := ⟨fun _ => st, fun _ => st, fun _ => st⟩
    let call := namedBody s T id vars s!"{stTy} → {binderTy} → {stTy}" s!"fun {st} {binder}"
      c!"{pre jd}{render body jd kd}"
    let restText := render rest i k
    Code.binding st "" c!"Ariadne.fold {st} {items} {call}" restText i
  else if idiom then
    let kb : KText := ⟨fun _ => c!"next' {st}", fun _ => c!"exit' {st}", fun _ => c!"next' {st}"⟩
    -- The result type: the function's, or any when the body cannot `return`.
    let (r, implicit) := if body.noRet then ("R", " {R : Type}") else (resultTy, "")
    let call := namedBody s T id vars s!"{binderTy} → ({stTy} → {r}) → ({stTy} → {r}) → {stTy} → {r}"
      s!"fun {binder} next' exit' {st}" c!"{pre jd}{render body jd kb}" implicit

    let restText := render rest j k
    c!"Ariadne.forIn {items} {call}\n{i}  " ++
      c!"(fun {st} =>\n{j}{restText})\n{i}  {st}"
  else
  let kb : KText := ⟨fun _ => c!"{nx} {st}", fun _ => c!"{ex} {st}", fun _ => c!"{nx} {st}"⟩
  let bodyText := c!"{pre j}{render body j kb}"
  let restText := render rest j k
  c!"Ariadne.forIn {items} (fun {binder} {nx} {ex} {st} =>\n{j}{bodyText})\n{i}  " ++
    c!"(fun {st} =>\n{j}{restText})\n{i}  {st}"

/-- A `while` loop: `Ariadne.whileDo (fun state => c) (fun next exit state => body) (fun state => rest) tuple`,
and `Ariadne.whileSafe` for the safety condition. -/
def whileText (render : Block → String → KText → Code) (s : Scope) (fn c : String) (body rest : Block)
    (idiom : Bool) (i : String) (k : KText) (T : Types) (id : Nat) (resultTy : String) : Code :=
  let d := i.length
  let (nx, ex) := (s!"next{d}'", s!"exit{d}'")
  let j := i ++ "  "
  if idiom then
    let st := s.stateText body.writes
    let vars := s.stateVars body.writes
    let stTy := if vars.isEmpty then "Unit" else " × ".intercalate (vars.map fun x => s.varTypeText T x)
    let kb : KText := ⟨fun _ => c!"next' {st}", fun _ => c!"exit' {st}", fun _ => c!"next' {st}"⟩
    let (r, implicit) := if body.noRet then ("R", " {R : Type}") else (resultTy, "")
    let call := namedBody s T id vars s!"({stTy} → {r}) → ({stTy} → {r}) → {stTy} → {r}"
      s!"fun next' exit' {st}" (render body "    " kb) implicit

    let restText := render rest j k
    c!"{fn} (fun {st} => {c})\n{i}  {call}\n{i}  " ++
      c!"(fun {st} =>\n{j}{restText})\n{i}  {st}"
  else
  let st := s.stateText body.writes
  let kb : KText := ⟨fun _ => c!"{nx} {st}", fun _ => c!"{ex} {st}", fun _ => c!"{nx} {st}"⟩
  let bodyText := render body j kb
  let restText := render rest j k
  c!"{fn} (fun {st} => {c})\n{i}  (fun {nx} {ex} {st} =>\n{j}{bodyText})\n{i}  " ++
    c!"(fun {st} =>\n{j}{restText})\n{i}  {st}"

def flagsIte (yes no rest : Block) : Bool × Bool × Bool :=
  ((yes.falls || no.falls) && rest.falls,
   yes.breaks || no.breaks || ((yes.falls || no.falls) && rest.breaks),
   yes.continues || no.continues || ((yes.falls || no.falls) && rest.continues))

mutual
  partial def checkStmts (T : Types) (s : Scope) (result : Ty) : List Parse.Stmt → CheckM Block
    | [] => pure blockNil
    | .let_ false x annotation e span :: rest => do
      let expected ← annotation.mapM (T.resolve span 64)
      let v ← checkExpr T s e expected
      let rest ← checkStmts T (← declare s span x v.ty) result rest
      pure { typed := s!"(.const {leanString x} {v.typed}\n  {rest.typed})",
             readable := fun i k => Code.binding (ident x) (T.lean v.ty) (.text v.readable) (rest.readable i k) i,
             safe := fun i k => andCode v.ok (Code.binding (ident x) (T.lean v.ty) (.text v.readable) (rest.safe i k) i),
             trivial := v.trivial && rest.trivial,
             falls := rest.falls, breaks := rest.breaks, continues := rest.continues,
             writes := rest.writes.erase x, noRet := rest.noRet, noBrk := rest.noBrk, noCont := rest.noCont }
    | .let_ true x annotation e span :: rest => do
      let expected ← annotation.mapM (T.resolve span 64)
      let v ← checkExpr T s e expected
      let s' ← declare s span x v.ty
      let rest ← checkStmts T { s' with mutables := x :: s'.mutables } result rest
      pure { typed := s!"(.let_ {leanString x} {v.typed}\n  {rest.typed})",
             readable := fun i k => Code.binding (ident x) (T.lean v.ty) (.text v.readable) (rest.readable i k) i,
             safe := fun i k => andCode v.ok (Code.binding (ident x) (T.lean v.ty) (.text v.readable) (rest.safe i k) i),
             trivial := v.trivial && rest.trivial,
             falls := rest.falls, breaks := rest.breaks, continues := rest.continues,
             writes := rest.writes.erase x, noRet := rest.noRet, noBrk := rest.noBrk, noCont := rest.noCont }
    | .assign (.var x _) e span :: rest => do
      let some (j, τ) := s.lookup x | throw { code := "A2001", message := s!"unknown variable '{x}'", span }
      if !s.mutables.contains x then mismatch span s!"'{x}' is not assignable (a const declaration)"
      let v ← checkExpr T s e (some τ)
      let rest ← checkStmts T s result rest
      -- A variable narrowed to a variant without fields stays unbound.
      let bind := if s.payloads.lookup x == some .unit then "" else s!"let {ident x} : {T.lean v.ty} := {v.readable}"
      let bindIn (i : String) (body : Code) := if bind.isEmpty then body else
        Code.binding (ident x) (T.lean v.ty) (.text v.readable) body i
      pure { typed := s!"(.assign {← s.varPath j} {v.typed}\n  {rest.typed})",
             readable := fun i k => bindIn i (rest.readable i k),
             safe := fun i k => andCode v.ok (bindIn i (rest.safe i k)),
             trivial := v.trivial && rest.trivial,
             falls := rest.falls, breaks := rest.breaks, continues := rest.continues,
             writes := [x].unite rest.writes, noRet := rest.noRet, noBrk := rest.noBrk, noCont := rest.noCont }
    | .continue_ _ :: rest => do
      let rest ← checkStmts T s result rest
      pure { typed := s!"(.cont {rest.typed})", readable := (fun i k => k.cont i), safe := (fun i k => k.cont i),
             trivial := rest.trivial, falls := false, breaks := false, continues := true,
             noRet := rest.noRet, noBrk := rest.noBrk, noCont := false }
    | .while_ c body span :: rest => do
      let c ← checkExpr T s c (some .bool)
      -- The condition is evaluated at every iteration; its safety would join the loop's.
      if !c.trivial then unsupportedTy span "a while condition with number arithmetic or calls of unsafe functions"
      let body ← checkStmts T s result (branchStmts body)
      let rest ← checkStmts T s result rest
      let id ← nextLoop
      pure { typed := s!"(.whileLoop {c.typed}\n  {body.typed}\n  {rest.typed})",
             readable := fun i k => whileText (·.readable) s "Ariadne.whileDo" c.readable body rest true i k T id (T.lean result),
             safe := fun i k => whileText (·.safe) s "Ariadne.whileSafe" c.readable body rest false i k T id "",
             trivial := false, falls := rest.falls, breaks := rest.breaks, continues := rest.continues,
             writes := body.writes.unite rest.writes, noRet := body.noRet && rest.noRet, noBrk := rest.noBrk,
             noCont := rest.noCont }
    | .forOf false x e body span :: rest => do
      let body := branchStmts body
      let a ← inferExpr T s e none
      let .array σ := a.ty | mismatch span s!"for-of over {a.ty.ts}"
      let body ← checkStmts T (← declare s span x σ) result body
      let rest ← checkStmts T s result rest
      let id ← nextLoop
      let text (render : Block → String → KText → Code) (idiom : Bool) (i : String) (k : KText) :=
        loopText render s a.term (ident x) (fun _ => "") body rest idiom i k T id (T.lean σ) (T.lean result)
      pure { typed := s!"(.forOf {leanString x} {a.typed}\n  {body.typed}\n  {rest.typed})",
             readable := text (·.readable) true, safe := fun i k => andCode a.ok (text (·.safe) false i k),
             trivial := a.trivial && body.trivial && rest.trivial,
             falls := rest.falls, breaks := rest.breaks, continues := rest.continues,
             writes := (body.writes.erase x).unite rest.writes, noRet := body.noRet && rest.noRet, noBrk := rest.noBrk,
             noCont := rest.noCont }
    | .for_ (.let_ true i _ (.literal (.number 0 0) _) _) (.binary "<" (.var i₁ _) (.var n _) _)
        update body span :: rest => do
      if !(i₁ == i && incrementOf update == some i) then unsupportedTy span "this for loop"
      let some (j, τ) := s.lookup n | throw { code := "A2001", message := s!"unknown variable '{n}'", span }
      if τ != .number then mismatch span s!"the bound '{n}' is {τ.ts}, not a number"
      if s.mutables.contains n then mismatch span s!"the bound '{n}' must be a const"
      -- The index is not assignable in the body (it is not added to the mutables).
      let bodyStmts := branchStmts body
      let body ← checkStmts T (← declare s span i .number) result bodyStmts
      let rest ← checkStmts T s result rest
      let id ← nextLoop
      let text (render : Block → String → KText → Code) (idiom : Bool) (i' : String) (k : KText) :=
        loopText render s s!"(Ariadne.range {ident n})" (ident i) (fun _ => "") body rest idiom i' k T id "Int" (T.lean result)
      pure { typed := s!"(.forRange {leanString i} {← s.varPath j}\n  {body.typed}\n  {rest.typed})",
             readable := text (·.readable) true, safe := text (·.safe) false, trivial := body.trivial && rest.trivial,
             falls := rest.falls, breaks := rest.breaks, continues := rest.continues,
             writes := (body.writes.erase i).unite rest.writes, noRet := body.noRet && rest.noRet, noBrk := rest.noBrk,
             noCont := rest.noCont }
    | .forOfPair false ix x (.call (.member e "entries" _) [] _) (.block body _) span :: rest => do
      let a ← inferExpr T s e none
      let .array σ := a.ty | mismatch span s!"entries of {a.ty.ts}"
      if ix == x then mismatch span "an index and an element of the same name"
      let body ← checkStmts T (← declare (← declare s span ix .number) span x σ) result body
      let rest ← checkStmts T s result rest
      let p := s!"n{s.locals.length}'"
      let id ← nextLoop
      let text (render : Block → String → KText → Code) (idiom : Bool) (i : String) (k : KText) :=
        loopText render s (if (listCall a.term "zipIdx").startsWith "List." then s!"({listCall a.term "zipIdx"})" else listCall a.term "zipIdx") s!"({ident x}, {p})"
          (fun j => s!"let {ident ix} := ({p} : Int)\n{j}") body rest idiom i k T id s!"{atomText (T.lean σ)} × Nat" (T.lean result)
      pure { typed := s!"(.forEntries {leanString ix} {leanString x} {a.typed}\n  {body.typed}\n  {rest.typed})",
             readable := text (·.readable) true, safe := fun i k => andCode a.ok (text (·.safe) false i k),
             trivial := a.trivial && body.trivial && rest.trivial,
             falls := rest.falls, breaks := rest.breaks, continues := rest.continues,
             writes := ((body.writes.erase x).erase ix).unite rest.writes, noRet := body.noRet && rest.noRet,
             noBrk := rest.noBrk, noCont := rest.noCont }
    | .return_ e span :: rest => do
      if s.void then
        let .literal .undefined _ := e | mismatch span "a value returned from a method returning void"
        let some (ti, _) := s.lookup "this" | mismatch span "'this' outside a method"
        let rest ← checkStmts T s result rest
        return { typed := s!"(.retVoid {← s.varPath ti} {rest.typed})", readable := fun _ _ => ident "this",
                 safe := fun _ _ => "true", trivial := rest.trivial, falls := false, breaks := false, continues := false,
                 noRet := false, noBrk := rest.noBrk, noCont := rest.noCont }
      let v ← checkExpr T s e (some result)
      let rest ← checkStmts T s result rest
      pure { typed := s!"(.ret {v.typed} {rest.typed})", readable := fun _ _ => v.readable, safe := fun _ _ => v.ok,
             trivial := v.trivial && rest.trivial, falls := false, breaks := false, continues := false,
             noRet := false, noBrk := rest.noBrk, noCont := rest.noCont }
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
             readable := fun i k => c!"{upd}\n{i}{rest.readable i k}",
             safe := fun i k => andCode operands c!"{upd}\n{i}{rest.safe i k}",
             trivial := key.trivial && others.all (·.trivial) && rest.trivial,
             falls := rest.falls, breaks := rest.breaks, continues := rest.continues,
             writes := ["this"].unite rest.writes, noRet := rest.noRet, noBrk := rest.noBrk, noCont := rest.noCont }
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
      pure { typed := s!"(.callVoid {fpath} {← s.varPath ti} {typedArgs}\n  {rest.typed})",
             readable := fun i k => c!"{upd}\n{i}{rest.readable i k}",
             safe := fun i k => andCode callSafe c!"{upd}\n{i}{rest.safe i k}",
             trivial := argsT && sig.trivial && rest.trivial,
             falls := rest.falls, breaks := rest.breaks, continues := rest.continues,
             writes := ["this"].unite rest.writes, noRet := rest.noRet, noBrk := rest.noBrk, noCont := rest.noCont }
    | .break_ _ :: rest => do
      let rest ← checkStmts T s result rest
      pure { typed := s!"(.brk {rest.typed})", readable := (fun i k => k.brk i), safe := (fun i k => k.brk i),
             trivial := rest.trivial, falls := false, breaks := true, continues := false,
             noRet := rest.noRet, noBrk := false, noCont := rest.noCont }
    | .block body _ :: rest => do
      let body ← checkStmts T s result body
      let rest ← checkStmts T s result rest
      pure { typed := s!"(.block {body.typed}\n  {rest.typed})",
             readable := fun i k => body.readable i { k with normal := fun j => rest.readable j k },
             safe := fun i k => body.safe i { k with normal := fun j => rest.safe j k },
             trivial := body.trivial && rest.trivial,
             falls := body.falls && rest.falls, breaks := body.breaks || (body.falls && rest.breaks),
             continues := body.continues || (body.falls && rest.continues),
             writes := body.writes.unite rest.writes, noRet := body.noRet && rest.noRet,
             noBrk := body.noBrk && rest.noBrk, noCont := body.noCont && rest.noCont }
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
               readable := iteText (·.readable) true s c.readable yes no rest,
               safe := fun i k => andCode c.ok (iteText (·.safe) false s c.readable yes no rest i k),
               trivial := c.trivial && yes.trivial && no.trivial && rest.trivial, falls, breaks, continues,
               writes := yes.writes.unite (no.writes.unite rest.writes), noRet := yes.noRet && no.noRet && rest.noRet,
               noBrk := yes.noBrk && no.noBrk && rest.noBrk, noCont := yes.noCont && no.noCont && rest.noCont }
    | .switch_ e cases span :: rest => checkSwitch T s result e cases span rest
    | st :: _ => unsupportedTy st.span "this statement"

  partial def checkNullIf (T : Types) (s : Scope) (result : Ty) (x : String) (isNull : Bool)
      (yesSs noSs : List Parse.Stmt) (span : Span) (rest : List Parse.Stmt) : CheckM Block := do
    let (n, path) ← s.nullNarrowing span x
    let narrowed := s.narrow n.index n.narrow
    if isNull then
      let yes ← checkStmts T s result yesSs
      if noSs.isEmpty && !yes.falls then
        -- `if (x == null) exit; rest` with `x` narrowed in the rest.
        let rest ← checkStmts T narrowed result rest
        let text (render : Block → String → KText → Code) (i : String) (k : KText) :=
          let j := i ++ "  "
          c!"match {ident x} with\n{i}| none =>\n{j}{render yes j k}\n{i}| some {ident x} =>\n{j}{render rest j (k.wrap n)}"
        return { typed := s!"(.ifNullExit {path} (by decide +kernel)\n  {yes.typed}\n  {rest.typed})",
                 readable := text (·.readable), safe := text (·.safe), trivial := yes.trivial && rest.trivial,
                 falls := rest.falls, breaks := yes.breaks || rest.breaks,
                 continues := yes.continues || rest.continues,
                 writes := yes.writes.unite rest.writes, noRet := yes.noRet && rest.noRet,
                 noBrk := yes.noBrk && rest.noBrk, noCont := yes.noCont && rest.noCont }
      let no ← checkStmts T narrowed result noSs
      let rest ← checkStmts T s result rest
      let text (render : Block → String → KText → Code) (idiom : Bool) (i : String) (k : KText) :=
        let arms (j : String) (k' : KText) :=
          let j' := j ++ "  "
          c!"match {ident x} with\n{j}| none =>\n{j'}{render yes j' k'}\n{j}| some {ident x} =>\n{j'}{render no j' (k'.wrap n)}"
        if idiom && yes.closed && no.closed then
          branchValueText s (yes.writes.unite no.writes) arms (render rest i k) i
        else if idiom || !(yes.falls || no.falls) then arms i { k with normal := fun j' => render rest j' k }
        else narrowedJoinText s x (yes.writes.unite no.writes) (fun j => render rest j k)
          (fun kn => arms i { k with normal := kn }) i
      let (falls, breaks, continues) := flagsIte yes no rest
      return { typed := s!"(.ifNull {path} (by decide +kernel)\n  {yes.typed}\n  {no.typed}\n  {rest.typed})",
               readable := text (·.readable) true, safe := text (·.safe) false,
               trivial := yes.trivial && no.trivial && rest.trivial, falls, breaks, continues,
               writes := yes.writes.unite (no.writes.unite rest.writes), noRet := yes.noRet && no.noRet && rest.noRet,
               noBrk := yes.noBrk && no.noBrk && rest.noBrk, noCont := yes.noCont && no.noCont && rest.noCont }
    else
      let yes ← checkStmts T narrowed result yesSs
      let no ← checkStmts T s result noSs
      let rest ← checkStmts T s result rest
      let text (render : Block → String → KText → Code) (idiom : Bool) (i : String) (k : KText) :=
        let arms (j : String) (k' : KText) :=
          let j' := j ++ "  "
          c!"match {ident x} with\n{j}| some {ident x} =>\n{j'}{render yes j' (k'.wrap n)}\n{j}| none =>\n{j'}{render no j' k'}"
        if idiom && yes.closed && no.closed then
          branchValueText s (yes.writes.unite no.writes) arms (render rest i k) i
        else if idiom || !(yes.falls || no.falls) then arms i { k with normal := fun j' => render rest j' k }
        else narrowedJoinText s x (yes.writes.unite no.writes) (fun j => render rest j k)
          (fun kn => arms i { k with normal := kn }) i
      let (falls, breaks, continues) := flagsIte yes no rest
      return { typed := s!"(.ifNotNull {path} (by decide +kernel)\n  {yes.typed}\n  {no.typed}\n  {rest.typed})",
               readable := text (·.readable) true, safe := text (·.safe) false,
               trivial := yes.trivial && no.trivial && rest.trivial, falls, breaks, continues,
               writes := yes.writes.unite (no.writes.unite rest.writes), noRet := yes.noRet && no.noRet && rest.noRet,
               noBrk := yes.noBrk && no.noBrk && rest.noBrk, noCont := yes.noCont && no.noCont && rest.noCont }

  /-- `switch (x.key)` over a union-typed local: cases in any order, grouped labels and
  `default`. A case with one label (not reached by falling through) narrows `x`. -/
  partial def checkSwitch (T : Types) (s : Scope) (result : Ty) (e : Parse.Expr)
      (cases : List (Option Parse.Expr × List Parse.Stmt)) (span : Span) (rest : List Parse.Stmt) : CheckM Block := do
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
          -- In the case, `x` is bound to the variant's payload.
          let payload := T.payload σ (ident x)
          let embed := s!"({T.injectText τ j payload} : {T.lean τ})"
          let nar : Narrowed := { index := i, name := x, wide := τ, narrow := σ, embed }
          let s' := { s.narrow i σ with payloads := (x, payload.rep) :: s.payloads }
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
    let reps := variants.map fun (t, fs) => (T.rep (vrec' key t fs)).getD .unit
    -- Cases that always go on after the `switch` (`TArms.closed`).
    let closed := bodies.all fun b => b.noRet && b.noCont
    let armsWrites := bodies.foldr (fun b acc => b.writes.unite acc) []
    let text (render : Block → String → KText → Code) (idiom : Bool) (ind : String) (k : KText) :=
      if idiom && closed then
        branchValueText s armsWrites (fun j kv => switchLeaves render x (T.ctorNames? τ) reps leaves kv (ident x) j)
          (render rest ind k) ind
      else if idiom || !f then
        let kr := fun j => render rest j k
        switchLeaves render x (T.ctorNames? τ) reps leaves { k with normal := kr, brk := kr } (ident x) ind
      else narrowedJoinText s x armsWrites (fun j => render rest j k) (fun kn =>
        switchLeaves render x (T.ctorNames? τ) reps leaves { k with normal := kn, brk := kn } (ident x) ind) ind
    pure { typed := s!"(.switchG {← s.varPath i} (by decide +kernel)\n  {armsTyped}\n  {rest.typed})",
           readable := text (·.readable) true, safe := text (·.safe) false,
           trivial := bodies.all (·.trivial) && rest.trivial,
           falls := f && rest.falls, breaks := f && rest.breaks,
           continues := bodies.any (·.continues) || (f && rest.continues),
           writes := armsWrites.unite rest.writes, noRet := bodies.all (·.noRet) && rest.noRet,
           noBrk := rest.noBrk, noCont := bodies.all (·.noCont) && rest.noCont }
end

/-! ## Functions and files -/

structure CheckedFn where
  sig : FnSig
  body : Block

/-- A function, or a method of a class whose state has type `this` (a method
returning `void` changes the state and denotes the state it leaves). -/
def checkFunction (T : Types) (fns : List FnSig) (f : Parse.Function) (this : Option Ty := none) :
    CheckM CheckedFn := do
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
    logHover { span := p.span, kind := "var", name := p.name, ty := τ }
  let .block body _ := f.body | unsupportedTy f.span "this function body"
  -- Falling off the end of a `void` method returns, as the converted program says.
  let body := if void then body ++ [.return_ (.literal .undefined f.span) f.span] else body
  let block ← checkStmts T s result body
  if block.falls then
    throw { code := "A2003", message := s!"'{f.name}' may finish without returning a value", span := f.span }
  if block.breaks || block.continues then
    throw { code := "A2003", message := "break or continue outside a loop or switch", span := f.span }
  logHover { span := f.span, kind := if this.isSome then "method" else "function", name := f.name, ty := result,
             params, safe := if block.trivial then "" else s!"{ident f.name}.safe" }
  pure { sig := { name := f.name, params, result, trivial := block.trivial, method := this.isSome, void },
         body := block }

/-- Names a named type's readable alias may not take: the functions' and methods', and the generated
declarations'. -/
def reservedNames (p : Parse.Program) : List String :=
  ["ast", "typed", "sigs", "erased", "wf", "bodies_ok", "ast_scoped", "denote_eq", "safety_eq", "ty", "sig",
    "body", "ne", "frames"] ++ p.functions.map (·.name) ++ p.classes.flatMap (fun c => c.methods.map (·.name))

def checkProgramM (p : Parse.Program) : CheckM (Types × List CheckedFn) := do
  let mut T ← Types.ofProgram p
  let reserved := reservedNames p
  T := { T with readable := T.named.filterMap fun (n, _) => if reserved.contains n then none else some n }
  modify fun l => { l with types := some T }
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
    modify fun l => { l with types := some T }
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

def checkProgram (p : Parse.Program) : Checked (Types × List CheckedFn) :=
  (checkProgramM p).run.run' {}

end Ariadne.Front
