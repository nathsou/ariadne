import Ariadne.Front.Elaborate

/-! File assembly for the untrusted translator. The checker supplies typed terms and
structured readable code; this module chooses the single-file or project layout. -/
namespace Ariadne.Front
open Ariadne.Parse (Diagnostic Checked Span)

/-! ## Printing the AST -/

def printLit : Lit → String
  | .undefined => ".undefined" | .null => ".null"
  | .bool b => s!"(.bool {b})"
  | .number n => s!"(.number {n})"
  | .bigint n => s!"(.bigint {n})"
  | .string s => s!"(.string {jsString s})"

def printUnOp : UnOp → String
  | .not => ".not" | .neg => ".neg" | .inc => ".inc" | .dec => ".dec"

def printBinOp : BinOp → String
  | .add => ".add" | .sub => ".sub" | .mul => ".mul" | .div => ".div" | .mod => ".mod" | .floorDiv => ".floorDiv"
  | .eq => ".eq" | .ne => ".ne"
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
    | .while_ c body => s!".while_ {printExpr c} {printStmts (indent ++ "  ") body}"
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

/-- The types inside `τ` (with `τ`), and a union's variants. -/
partial def tyClosure (acc : List Ty) (τ : Ty) : List Ty :=
  if acc.contains τ then acc else
  let acc := acc ++ [τ]
  match τ with
  | .option _ σ | .array σ | .map σ => tyClosure acc σ
  | .record fs => (Fields.toList fs).foldl (fun a (_, σ) => tyClosure a σ) acc
  | .union key vs => (Variants.toList vs).foldl (fun a (t, fs) => tyClosure a (vrec' key t fs)) acc
  | _ => acc


/-- The program's named types as Lean declarations: a structure per named record whose fields can name a
structure's (for a variant, the fields after its tag), an inductive per named union whose tags can name
constructors (with a structure `«U».Variant.«tag»` per variant with more than one field), and an
abbreviation for the others, with an accessor `«T».«f»` per field of a record and a constant `«T».«lit»`
per literal of a literal union, reducible and in the simp set `readable`. -/
def readableNames (T : Types) : String := Id.run do
  -- A named type comes after the named types inside it.
  let inside (σ τ : Ty) : Bool := σ != τ && (tyClosure [] τ).contains σ
  let mut order : List (String × Ty) := []
  let mut todo := T.named.filter fun (n, _) => T.readable.contains n
  while !todo.isEmpty do
    let ready := todo.filter fun (_, τ) => !todo.any fun (_, σ) => inside σ τ
    let next := if ready.isEmpty then todo else ready
    order := order ++ next
    todo := todo.filter fun (n, _) => !next.any (·.1 == n)
  let structureText (name : String) (fields : List (String × Ty)) : String :=
    s!"structure {name} where\n" ++ String.join (fields.map fun (f, σ) => s!"  {ident f} : {T.lean σ}\n")
  let mut out := ""
  let mut declared : List String := []
  for (n, τ) in order do
    let N := ident n
    let doc := s!"\n/-- The source's `{n}`. -/\n"
    -- The payload structures of a union's variants.
    if let .union key vs := τ then
      for (t, fs) in Variants.toList vs do
        if let some (.struct V fields) := T.rep (vrec' key t fs) then
          if !declared.contains V && V != N then
            out := out ++ s!"\n/-- The fields of the source's `{n}` tagged {tagLitTS t}. -/\n" ++ structureText V fields
            declared := declared ++ [V]
    let canon := T.lean τ
    if canon != N then
      out := out ++ doc ++ s!"abbrev {N} : Type := {canon}\n"
      continue
    match T.rep τ, τ with
    | some (.struct _ fields), _ =>
      out := out ++ doc ++ structureText N fields
      declared := declared ++ [N]
    | _, .record fs =>
      if (T.structName? τ).isSome then
        out := out ++ doc ++ structureText N (Fields.toList fs)
        declared := declared ++ [N]
      else
        out := out ++ doc ++ s!"abbrev {N} : Type := {T.leanBody τ}\n"
        for ((f, σ), k) in (Fields.toList fs).zipIdx do
          out := out ++ s!"@[reducible, readable] def {N}.{ident f} (r : {N}) : {T.lean σ} := {projText "r" k}\n"
    | _, .lits a as =>
      out := out ++ doc ++ s!"abbrev {N} : Type := Fin {as.length + 1}\n"
      for (lit, i) in (a :: as).zipIdx do
        if let some l := litName lit then
          out := out ++ s!"@[reducible, readable] def {N}.{ident l} : {N} := ({i} : Fin {as.length + 1})\n"
    | _, .union key vs =>
      match T.inductive? τ with
      | some (_, ctors) =>
        let arms := ((Variants.toList vs).zip ctors).map fun ((t, fs), c) =>
          let c := (c.splitOn ".").getLastD c
          match T.rep (vrec' key t fs) with
          | some (.single σ) => match Fields.toList fs with
            | [(f, _)] => s!"  | {c} ({ident f} : {T.lean σ})\n"
            | _ => s!"  | {c} (x : {T.lean σ})\n"
          | some .unit | none => s!"  | {c}\n"
          | some _ => s!"  | {c} (x : {T.lean (vrec' key t fs)})\n"
        out := out ++ doc ++ s!"inductive {N} where\n" ++ String.join arms
      | none => out := out ++ doc ++ s!"abbrev {N} : Type := {T.leanBody τ}\n"
    | _, _ => out := out ++ doc ++ s!"abbrev {N} : Type := {T.leanBody τ}\n"
  return out

/-- `(x.f, x.g, ())`: the tuple of a structure's fields. -/
def fieldsTuple (x : String) (fields : List (String × Ty)) : String :=
  "(" ++ ", ".intercalate (fields.map (fun (f, _) => s!"{x}.{ident f}") ++ ["()"]) ++ ")"

/-- `(S.mk x.1 x.2.1)`: a structure from the tuple of its fields. -/
def mkOfTuple (S : String) (x : String) (n : Nat) : String :=
  if n == 0 then s!"{S}.mk" else "(" ++ " ".intercalate (s!"{S}.mk" :: (List.range n).map (projText x)) ++ ")"

/-- `names`, the program's structures and inductives with the records and unions they are, and `isos`,
how their values correspond to the records' and unions' (`Isos`). `tys`: the types the program uses. -/
def namesText (T : Types) (tys : List Ty) : String := Id.run do
  let closure := (T.named.map (·.2) ++ tys).foldl tyClosure []
  -- Records: (fields, type, view, make).
  let mut recs : List (Fields × String × String × String) := []
  for (n, τ) in T.named do
    if let .record fs := τ then
      if let some S := T.structName? τ then
        if S == ident n && !recs.any (·.1 == fs) then
          let fields := Fields.toList fs
          recs := recs ++ [(fs, S, s!"fun (r : {S}) => {fieldsTuple "r" fields}", s!"fun x => {mkOfTuple S "x" fields.length}")]
  for σ in closure do
    if let (.record fs, some r) := (σ, T.rep σ) then
      if !recs.any (·.1 == fs) then
        let ty := T.lean σ
        let (view, make) := match r with
          | .unit => (s!"fun (_ : {ty}) => ((), ())", s!"fun _ => ()")
          | .single _ => (s!"fun (x : {ty}) => ((), x, ())", "fun x => x.2.1")
          | .struct S fields => (s!"fun (r : {S}) => ((), {fieldsTuple "r" fields})",
              s!"fun x => {mkOfTuple S "x.2" fields.length}")
          | .tuple _ => (s!"fun (x : {ty}) => ((), x)", "fun x => x.2")
        recs := recs ++ [(fs, ty, view, make)]
  -- Unions: (variants, type, the variants' constructors and representations).
  let mut unions : List (Variants × String × List (String × Rep)) := []
  for (n, τ) in T.named do
    if let .union key vs := τ then
      if let some (m, ctors) := T.inductive? τ then
        if m == ident n && !unions.any (·.1 == vs) then
          let reps := (Variants.toList vs).map fun (t, fs) => (T.rep (vrec' key t fs)).getD .unit
          unions := unions ++ [(vs, m, ctors.zip reps)]
  let mut out := "/-- The program's structures and inductives, with the records and unions they are. -/\n"
  out := out ++ "noncomputable def names : Names :=\n  ⟨[" ++ ",\n    ".intercalate (recs.map fun (fs, ty, _) =>
    s!"({printFields T.name fs}, {ty})") ++ "],\n   [" ++ ",\n    ".intercalate (unions.map fun (vs, ty, _) =>
    s!"({printVariants T.name vs}, {ty})") ++ "]⟩\n\n"
  out := out ++ "/-- How the structures' and inductives' values correspond to the records' and unions'. -/\n"
  out := out ++ "noncomputable def isos : Isos names := Isos.ofLists\n"
  -- A right-nested list of `.cons` entries.
  let nested (entries : List String) : String :=
    entries.foldr (fun e acc => s!"(.cons {e}\n   {acc})") ".nil"
  out := out ++ "  " ++ nested (recs.map fun (_, _, v, m) => s!"({v}) ({m}) (fun _ => rfl) (fun _ => rfl)") ++ "\n"
  -- A variant's fields' tuple as a pattern (`(a0, a1, ())`), and the constructor's value from it.
  let fieldsPat (r : Rep) (wild : Bool := false) : String :=
    let v (k : Nat) := if wild then "_" else s!"a{k}"
    match r with
    | .unit => "()"
    | .single _ => s!"({v 0}, ())"
    | .struct _ fields => "(" ++ ", ".intercalate ((List.range fields.length).map v ++ ["()"]) ++ ")"
    | .tuple _ => v 0
  let ctorOf (c : String) (r : Rep) : String := match r with
    | .unit => c
    | .single _ | .tuple _ => s!"{c} a0"
    | .struct S fields => s!"{c} ({" ".intercalate (s!"{S}.mk" :: (List.range fields.length).map (s!"a{·}"))})"
  let entry (cs : List (String × Rep)) : String :=
    let n := cs.length
    let uelim := "(fun u h => match u with\n" ++ "\n".intercalate (cs.zipIdx.map fun ((c, r), j) =>
      let (pat, tup) := match r with
        | .unit => (c, "()")
        | .single _ => (s!"{c} x", "(x, ())")
        | .struct _ fields => (s!"{c} x", fieldsTuple "x" fields)
        | .tuple _ => (s!"{c} x", "x")
      s!"      | {pat} => h {vidxPath j n} {tup}") ++ ")"
    let umake := "(fun s => match s with\n" ++ "\n".intercalate (cs.zipIdx.map fun ((c, r), j) =>
      s!"      | {injText j n (fieldsPat r)} => {ctorOf c r}") ++ ")"
    let law1 := "(fun {_} x _ => match x with\n" ++ "\n".intercalate (cs.zipIdx.map fun ((_, r), j) =>
      s!"      | {injText j n (fieldsPat r true)} => rfl") ++ ")"
    let law2 := "(fun u => match u with\n" ++ "\n".intercalate (cs.map fun (c, r) =>
      s!"      | {if r == .unit then c else s!"{c} _"} => rfl") ++ ")"
    s!"{uelim}\n    {umake}\n    {law1}\n    {law2}"
  out := out ++ "  " ++ nested (unions.map fun (_, _, cs) => entry cs) ++ "\n"
  return out

/-- The state fields a method's statements write, and the methods they call that may change the state. -/
partial def stmtsEffects (ss : List Stmt) : List String × List String :=
  ss.foldl (fun (w, c) st =>
    let (w', c') : List String × List String := match st with
      | .stateSet f _ _ | .stateDelete f _ => ([f], [])
      | .callThis m _ => ([], [m])
      | .ite _ yes no => stmtsEffects (yes ++ no)
      | .block body | .forOf _ _ body | .forEntries _ _ _ body | .forRange _ _ body | .while_ _ body => stmtsEffects body
      | .switch _ cases => stmtsEffects (cases.flatMap (·.2))
      | _ => ([], [])
    (w ++ w', c ++ c')) ([], [])

/-- Per function, in declaration order: a method that never writes the state's field `g` (what
`TProgram.frames` computes, newest first). -/
def frameFlags (ast : Program) (fns : List CheckedFn) (g : String) : List Bool := Id.run do
  let mut keep : List (String × Bool) := []
  for fn in fns do
    let b := fn.sig.void && match ast.find? (·.name == fn.sig.name) with
      | some f =>
        let (w, c) := stmtsEffects f.body
        !w.contains g && c.all fun m => (keep.lookup m).getD false
      | none => false
    keep := keep ++ [(fn.sig.name, b)]
  return keep.map (·.2)

/-- The public model and its certificate are collected separately, before rendering files. -/
structure Generated where
  source : String
  namespace_ : String
  types : String
  certificateHead : String
  definitions : String
  certificateTail : String

def Generated.wrap (g : Generated) (imports body : String) : String :=
  imports ++ s!"\n-- Generated by ariadne from {g.source}. Do not edit.\n\nnamespace {g.namespace_}\nopen Ariadne\n\n" ++
    "set_option maxRecDepth 8192\nset_option linter.unusedVariables false\n\n" ++ body ++ s!"end {g.namespace_}\n"

def certificateImports : String :=
  "import Ariadne.Proof.Adequacy\nimport Ariadne.Proof.Frame\nimport Ariadne.Proof.Named\nimport Ariadne.Lib.Readable\nimport Ariadne.Lib.SafetySpec\n"

/-- Standalone format, also used by the browser. -/
def Generated.single (g : Generated) : String :=
  g.wrap certificateImports (g.types ++ g.certificateHead ++ g.definitions ++ g.certificateTail)

/-- A project imports the umbrella to check both files, or opens Model.lean to read the program. -/
def Generated.split (g : Generated) : String × String × String :=
  (g.wrap "import Ariadne.Typed.Named\nimport Ariadne.Lib.Readable\nimport Ariadne.Lib.SafetySpec\n" (g.types ++ g.definitions),
   g.wrap (s!"import {g.namespace_}.Model\n" ++ certificateImports) (g.certificateHead ++ g.certificateTail),
   s!"-- Generated by ariadne. Imports the model and its checked certificate.\nimport {g.namespace_}.Certificate\n")

/-- Collect the model, typed certificate and per-function source theorems. -/
def printParts (source namespace_ : String) (ast : Program) (T : Types) (fns : List CheckedFn) (tys : List Ty := []) (nes : List (String × String) := []) :
    Generated := Id.run do
  -- A line comment: a path may contain `/-`, which would open a block comment.
  let name := ((source.splitOn "/").getLast?.getD source).map fun c => if c == '\n' || c == '\r' then ' ' else c
  let mut out := ""
  out := out ++ "/-- The source file in the model's syntax. -/\nnoncomputable def ast : Program := [\n  " ++
    ",\n  ".intercalate (ast.map printFunction) ++ "]\n\n"
  for (n, τ) in T.named do
    out := out ++ s!"noncomputable abbrev ty.{ident n} : Ty := {printTy τ}\n"
  let types := readableNames T ++ "\n"
  out := out ++ namesText T (tys ++ fns.flatMap fun fn => fn.sig.result :: fn.sig.params.map (·.2)) ++ "\n"
  for fn in fns do
    let s := fn.sig
    let ctx := "[" ++ ", ".intercalate (s.params.map fun (x, τ) => s!"({leanString x}, {T.print τ})") ++ "]"
    let kind := if s.method then s!", method := true, void := {s.void}" else ""
    out := out ++ s!"noncomputable def {sigName s.name} : Sig := " ++ "{ name := " ++ leanString s.name ++
      s!", params := {ctx}, result := {T.print s.result}, trivial := {s.trivial}{kind} " ++ "}\n"
  out := out ++ "\n"
  for (a, b) in nes.eraseDups do
    out := out ++ s!"theorem ne.{quoted a}.{quoted b} : ({leanString a} : String) ≠ {leanString b} := by decide\n"
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
  let certificateHead := out
  out := "/-! ## Readable definitions -/\n\n"
  for fn in fns do
    let s := fn.sig
    let params := " ".intercalate (s.params.map fun (x, τ) => s!"({ident x} : {T.lean τ})")
    let dflt := s!"(Ty.defaultS names isos {T.print s.result})"
    let (text, loops) := Code.emit (ident s.name) (fn.body.readable "  " ⟨fun _ => dflt, fun _ => dflt, fun _ => dflt⟩)
    for l in loops do
      out := out ++ s!"/-- A loop body of `{s.name}`. -/\n{l}\n\n"
    out := out ++ s!"def {ident s.name} {params} : {T.lean s.result} :=\n  " ++ text ++ "\n\n"
    if !s.trivial then
      out := out ++ s!"/-- The inputs on which `{s.name}` stays within what the model covers. -/\n"
      out := out ++ s!"def {ident s.name}.safe {params} : Bool :=\n  " ++
        (fn.body.safe "  " ⟨fun _ => "true", fun _ => "true", fun _ => "true"⟩).preview ++ "\n\n"
      out := out ++ s!"-- A checked, simplified proposition for proofs: `rw [{ident s.name}.safe_iff]`.\n" ++
        s!"safety_spec {ident s.name}.safe => {ident s.name}.safe_iff\n\n"
  let definitions := out
  out := "/-! ## Denotation

Each body is checked against its readable definition with the earlier functions'
readable definitions as its environment, so no check unfolds a callee. -/\n\n"
  let tupleOf (names : List String) (suffix : String) : String :=
    "(" ++ ", ".intercalate (names.map (s!"{ident ·}.{suffix}") ++ ["()"]) ++ ")"
  let mut prior : List String := []
  for fn in fns do
    let s := fn.sig
    let projections := (List.range s.params.length).map fun k => projText "xs" k
    let applied := if s.params.isEmpty then ident s.name else " ".intercalate (ident s.name :: projections)
    out := out ++ s!"noncomputable def {ident s.name}.uncurried : Sig.denS names {sigName s.name} := fun xs => {applied}\n\n"
    if s.trivial then
      out := out ++ s!"/-- Trivially safe: every input is in what the model covers. -/\n"
      out := out ++ s!"noncomputable def {ident s.name}.safety : Ctx.denS names {sigName s.name}.params → Bool := fun _ => true\n\n"
    else
      let safeApplied := " ".intercalate (s!"{ident s.name}.safe" :: projections)
      out := out ++ s!"noncomputable def {ident s.name}.safety : Ctx.denS names {sigName s.name}.params → Bool := fun xs => {safeApplied}\n\n"
    out := out ++ s!"theorem {ident s.name}.body_eq :\n    body.{ident s.name}.denoteRSFn names isos {tupleOf prior "uncurried"} = {ident s.name}.uncurried := by\n  kernel_rfl\n\n"
    out := out ++ s!"theorem {ident s.name}.safe_eq :\n    body.{ident s.name}.safeFnS names isos {tupleOf prior "uncurried"} {tupleOf prior "safety"} = {ident s.name}.safety := by\n  kernel_rfl\n\n"
    prior := s.name :: prior
  let mut den := "rfl"
  let mut safe := "rfl"
  -- These private proofs infer their types from the assembly lemmas. Repeating the full
  -- program/environment in each prefix's annotation would itself be quadratic output.
  out := out ++ "-- Private proof types are inferred to avoid repeating program prefixes.\n" ++
    "section\nset_option linter.defProp false\n\n"
  for (fn, i) in fns.zipIdx do
    let f := ident fn.sig.name
    let dn := s!"denote_prefix_{i}'"
    let sn := s!"safety_prefix_{i}'"
    let base := if i == 0 then " (P := .nil)" else ""
    out := out ++ s!"private def {dn} :=\n  TProgram.denote_consS isos{base} {den} {f}.body_eq\n\n"
    out := out ++ s!"private def {sn} :=\n  TProgram.safety_consS isos{base} {den} {safe} {f}.safe_eq\n\n"
    den := dn
    safe := sn
  out := out ++ "end\n\n"
  out := out ++ s!"theorem denote_eq : typed.denote = Sigs.canon names isos sigs {tupleOf prior "uncurried"} :=\n  {den}\n\n"
  out := out ++ s!"theorem safety_eq : typed.safety = Sigs.canonSafety names isos sigs {tupleOf prior "safety"} :=\n  {safe}\n\n"
  -- Frames: which fields of the state each method leaves alone.
  if let some σ := (fns.find? (·.sig.void)).map (·.sig.result) then
    if let .record fsσ := σ then
      out := out ++ "/-! ## Frames\n\nThe fields of the state each method leaves alone. -/\n\n"
      let fields := Fields.toList fsσ
      for ((g, _), k) in fields.zipIdx do
        let flags := frameFlags ast fns g
        out := out ++ s!"theorem frames.{ident g} : typed.frames {leanString g} = [{", ".intercalate (flags.reverse.map toString)}] := by\n  decide +kernel\n\n"
        let n := fns.length
        for ((fn, b), i) in (fns.zip flags).zipIdx do
          if !b then continue
          let s := fn.sig
          let fvar := s!"({fnPath (n - 1 - i)} : FVar sigs {leanString s.name} {sigName s.name})"
          let binders := " ".intercalate (s.params.map fun (x, τ) => s!"({ident x} : {T.lean τ})")
          let call := s!"({ident s.name} {" ".intercalate (s.params.map (ident ·.1))})"
          let args := "(" ++ ", ".intercalate (s.params.tail.map (ident ·.1) ++ ["()"]) ++ ")"
          out := out ++ s!"/-- `{s.name}` leaves `this.{g}` as it is. -/\n"
          out := out ++ s!"theorem {ident s.name}.keeps.{ident g} {binders} :\n    {T.fieldText σ call k} = {T.fieldText σ (ident "this") k} :=\n"
          out := out ++ s!"  frame_of_fnS isos {fidxPath k} denote_eq frames.{ident g} {fvar} rfl (f := {ident s.name}.uncurried) rfl\n" ++
            s!"    (acc := fun (r : {T.lean σ}) => {T.fieldText σ "r" k}) (fun _ => rfl) {ident "this"} {args}\n\n"
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
      out := out ++ s!"theorem {ident s.name}.source {binders} (this' : JSValue) (vs' : List JSValue)\n    (args' : ArgsRepS names isos {sigName s.name}.params (this' :: vs') {tuple}){safeHyp} :\n"
      out := out ++ s!"    ∃ w' t', Converges (fun fuel' => runMethod ast fuel' {leanString s.name} this' vs') (.ok (w', t')) ∧\n      Ty.RepS names isos {T.print s.result} t' ({call}) :=\n"
      out := out ++ s!"  source_state_ofS isos erased wf denote_eq safety_eq {fvar} rfl {tuple} this' vs' args' {safeArg}\n\n"
    else
      out := out ++ s!"/-- Every run of `{s.name}` on arguments representing its inputs converges to a value\nrepresenting the readable definition's result. -/\n"
      out := out ++ s!"theorem {ident s.name}.source {binders} (vs' : List JSValue)\n    (args' : ArgsRepS names isos {sigName s.name}.params vs' {tuple}){safeHyp} :\n"
      out := out ++ s!"    ∃ w', Converges (fun fuel' => run ast fuel' {leanString s.name} vs') (.ok w') ∧\n      Ty.RepS names isos {T.print s.result} w' ({call}) :=\n"
      out := out ++ s!"  source_ofS isos erased wf denote_eq safety_eq {fvar} rfl {tuple} vs' args' {safeArg}\n\n"
  return { source := name, namespace_, types, certificateHead, definitions, certificateTail := out }

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
def translatePartsM (source namespace_ text : String) : CheckM Generated := do
  let parsed ← Parse.parse text
  let ast ← convertProgram parsed
  let (T, fns) ← checkProgramM parsed
  let tys := (← get).hovers.toList.map (·.ty)
  pure (printParts source namespace_ ast T fns tys (← get).inequalities)

def translateM (source namespace_ text : String) : CheckM String :=
  return (← translatePartsM source namespace_ text).single

def translateParts (source namespace_ text : String) : Checked Generated :=
  (translatePartsM source namespace_ text).run.run' {}

def translate (source namespace_ text : String) : Checked String :=
  (translateM source namespace_ text).run.run' {}

/-- `translate`, with the log of what the checked parts of the program denote (up to the error, if any).
When the conversion fails before the checker runs, the checker still runs for its log. -/
def translateLogged (source namespace_ text : String) : Checked String × CheckLog :=
  let (result, log) := (translateM source namespace_ text).run.run {}
  if !log.hovers.isEmpty || result matches .ok _ then (result, log) else
    match Parse.parse text with
    | .ok parsed => (result, ((checkProgramM parsed).run.run {}).2)
    | .error _ => (result, log)

end Ariadne.Front
