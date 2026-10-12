import Ariadne.Shallow.StatePlan

namespace Ariadne.Shallow.ClassPlan

/-- Generated names contain `#`, which cannot occur in source identifiers. -/
def stateName (name : String) := name ++ "#state"
def methodName (owner method : String) := owner ++ "#" ++ method

mutual
  def expression (owner : String) : Nat → Expr → Checked Expr
    | 0, e => StatePlan.refusal "A5101" "class lowering nesting budget exhausted" e.span
    | n + 1, e => do
      match e with
      | .call (.member (.var "this" s) method _) args span =>
        return .call (.var (methodName owner method) span) (.var "this" s :: (← args.mapM (expression owner n))) span
      | .call f args s => return .call (← expression owner n f) (← args.mapM (expression owner n)) s
      | .member e f s => return .member (← expression owner n e) f s
      | .index a b s => return .index (← expression owner n a) (← expression owner n b) s
      | .unary op e s => return .unary op (← expression owner n e) s
      | .binary op a b s => return .binary op (← expression owner n a) (← expression owner n b) s
      | .conditional a b c s => return .conditional (← expression owner n a) (← expression owner n b) (← expression owner n c) s
      | .array es s => return .array (← es.mapM (expression owner n)) s
      | .record fields s => return .record (← fields.mapM fun (k,v) => do return (k, ← expression owner n v)) s
      | .lambda ps body s => return .lambda ps (← statement owner n body) s
      | .spread e s => return .spread (← expression owner n e) s
      | .newClass name args s => return .newClass name (← args.mapM (expression owner n)) s
      | _ => return e
  termination_by structural fuel _ => fuel

  def statement (owner : String) : Nat → Stmt → Checked Stmt
    | 0, s => StatePlan.refusal "A5101" "class lowering nesting budget exhausted" s.span
    | n + 1, s => do
      match s with
      | .block ss sp => return .block (← ss.mapM (statement owner n)) sp
      | .let_ m name ty e sp => return .let_ m name ty (← expression owner n e) sp
      | .assign a b sp => return .assign (← expression owner n a) (← expression owner n b) sp
      | .expr e sp => return .expr (← expression owner n e) sp
      | .return_ e sp => return .return_ (← expression owner n e) sp
      | .if_ e a b sp => return .if_ (← expression owner n e) (← statement owner n a) (← statement owner n b) sp
      | .while_ e b sp => return .while_ (← expression owner n e) (← statement owner n b) sp
      | .for_ i c u b sp => return .for_ (← statement owner n i) (← expression owner n c) (← statement owner n u) (← statement owner n b) sp
      | .forOf m name e b sp => return .forOf m name (← expression owner n e) (← statement owner n b) sp
      | .switch_ e cs sp => return .switch_ (← expression owner n e) (← cs.mapM fun (e, ss) => do return (← e.mapM (expression owner n), ← ss.mapM (statement owner n))) sp
      | .measured e b sp => return .measured (← expression owner n e) (← statement owner n b) sp
      | _ => return s
  termination_by structural fuel _ => fuel
end

/-- Preserve the original source certificate while giving each class a named
record state and explicit receiver functions. Constructors initialize fresh state
before running their checked body through the same borrowed-state lowering. -/
def lower (p : Program) : Checked Program := do
  let mut aliases := p.aliases
  let mut functions := p.functions
  for c in p.classes do
    let fields ← c.fields.mapM fun field => do
      let ty ← match field.ty with
        | some ty => pure ty
        | none => Check.infer 256 { program := p } field.value
      return (field.name, ty)
    aliases := aliases ++ [(stateName c.name, .record fields)]
    for m in c.methods do
      let body ← statement c.name 512 m.body
      let lowered := { m with
        name := methodName c.name m.name
        params := { name := "this", ty := .named (stateName c.name) } :: m.params
        body }
      functions := functions ++ [lowered]
    let initial := Expr.record (c.fields.map fun field => (field.name, field.value)) c.span
    let mut body := Stmt.return_ initial c.span
    let mut params := []
    if let some init := c.constructor_ then
      params := init.params
      let lowered : Ariadne.Function := { init with
        name := methodName c.name "#init"
        params := { name := "this", ty := .named (stateName c.name) } :: init.params
        body := ← statement c.name 512 init.body }
      functions := functions ++ [lowered]
      body := .block [
        .let_ false "this" (some (.named (stateName c.name))) initial c.span,
        .expr (.call (.var (methodName c.name "#init") c.span)
          (.var "this" c.span :: params.map (fun param => .var param.name param.span)) c.span) c.span,
        .return_ (.var "this" c.span) c.span] c.span
    let constructor : Ariadne.Function := {
      name := methodName c.name "#new", params
      result := .named (stateName c.name)
      body }
    functions := functions ++ [constructor]
  return { p with aliases, functions }

end Ariadne.Shallow.ClassPlan
