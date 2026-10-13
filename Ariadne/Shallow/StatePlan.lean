import Ariadne.Check

namespace Ariadne.Shallow.StatePlan

def refusal (code message : String) (span : Span) : Checked α :=
  .error { code, message, span }

def mutator (name : String) : Bool := ["set", "add", "delete", "clear", "push", "pop"].contains name

mutual
  /-- The parameters a function mutates. Calls to the function from its own
  body are resolved by iterating from no writes until the set is stable: a
  parameter is mutated if the body mutates it, or passes it to itself in a
  position that is mutated. -/
  def effects (p : Program) : Nat → Ariadne.Function → Checked (List String)
    | 0, f => refusal "A5101" "recursive effects require a termination measure" f.span
    | n + 1, f => do
      let step := fun (assumed : List String) => do
        let roots ← statementEffects p (some (f.name, f.params.map Param.name, assumed)) n f.body
        let params ← f.params.filterM fun param => do
          let ty ← Check.resolve 100 p param.ty
          return roots.contains param.name && Check.referenceType ty && !Check.immutable ty
        return params.map Param.name
      let mut writes : List String := []
      for _ in [0:f.params.length + 1] do
        let next ← step writes
        if next == writes then return writes
        writes := next
      return writes
  termination_by structural fuel _ => fuel

  /-- `self` names the function under analysis, its parameters and the writes
  assumed for its calls to itself. -/
  def expressionEffects (p : Program) (self : Option (String × List String × List String)) :
      Nat → Expr → Checked (List String)
    | 0, expr => refusal "A5101" "effect analysis nesting budget exhausted" expr.span
    | n + 1, expr => do
      match expr with
      | .call (.var name _) args _ =>
        let nested := (← args.mapM (expressionEffects p self n)).flatten
        if let some (current, params, assumed) := self then
          if current == name then
            return nested ++ ((args.zip params).filterMap fun (arg, param) =>
              if assumed.contains param then Check.root arg else none)
        let some f := p.functions.find? (·.name == name) | return nested
        let writes ← effects p n f
        return nested ++ ((args.zip f.params).filterMap fun (arg, param) =>
          if writes.contains param.name then Check.root arg else none)
      | .call (.member receiver method _) args _ =>
        let nested := (← expressionEffects p self n receiver) ++ (← args.mapM (expressionEffects p self n)).flatten
        let mut writes := mutator method
        for c in (match receiver with | .var .. => p.classes | _ => []) do
          if let some f := p.functions.find? (·.name == c.name ++ "#" ++ method) then
            if (← effects p n f).contains "this" then writes := true
        return nested ++ if writes then (Check.root receiver).toList else []
      | .call callee args _ =>
        return (← expressionEffects p self n callee) ++ (← args.mapM (expressionEffects p self n)).flatten
      | .binary _ a b _ | .index a b _ =>
        return (← expressionEffects p self n a) ++ (← expressionEffects p self n b)
      | .conditional a b c _ =>
        return (← expressionEffects p self n a) ++ (← expressionEffects p self n b) ++ (← expressionEffects p self n c)
      | .unary _ e _ | .member e _ _ | .spread e _ => expressionEffects p self n e
      | .array xs _ | .newClass _ xs _ => return (← xs.mapM (expressionEffects p self n)).flatten
      | .record fields _ => return (← fields.mapM fun (_, e) => expressionEffects p self n e).flatten
      | .lambda .. => return [] -- The checker prohibits mutations of captured owners in callbacks.
      | _ => return []
  termination_by structural fuel _ => fuel

  def statementEffects (p : Program) (self : Option (String × List String × List String)) :
      Nat → Stmt → Checked (List String)
    | 0, stmt => refusal "A5101" "effect analysis nesting budget exhausted" stmt.span
    | n + 1, stmt => do
      match stmt with
      | .block stmts _ => return (← stmts.mapM (statementEffects p self n)).flatten
      | .assign target value _ | .update target _ value _ =>
        let roots := match target with | .var .. => [] | _ => (Check.root target).toList
        return roots ++ (← expressionEffects p self n target) ++ (← expressionEffects p self n value)
      | .let_ _ _ _ value _ | .expr value _ | .return_ value _ => expressionEffects p self n value
      | .if_ guard yes no _ =>
        return (← expressionEffects p self n guard) ++ (← statementEffects p self n yes) ++ (← statementEffects p self n no)
      | .for_ init guard update body _ =>
        return (← statementEffects p self n init) ++ (← expressionEffects p self n guard) ++
          (← statementEffects p self n update) ++ (← statementEffects p self n body)
      | .while_ guard body _ | .forOf _ _ guard body _ =>
        return (← expressionEffects p self n guard) ++ (← statementEffects p self n body)
      | .switch_ value cases _ =>
        return (← expressionEffects p self n value) ++
          (← cases.mapM fun (label, body) => do
            let labels ← label.toList.mapM (expressionEffects p self n)
            return labels.flatten ++ (← body.mapM (statementEffects p self n)).flatten).flatten
      | .measured _ body _ => statementEffects p self n body
      | _ => return []
  termination_by structural fuel _ => fuel
end

def loanName (name : String) : String := "#loan:" ++ name

def tuple (names : List String) (span : Span) : Expr :=
  names.foldr (fun name rest => .array [.var (loanName name) span, rest] span) (.literal .undefined span)

/-- Return the original borrowed objects alongside the source result. This
rewrites returns in the current function only, leaving callback returns alone. -/
def returns (loans : List String) : Nat → Stmt → Checked Stmt
  | 0, stmt => refusal "A5101" "return-state transformation nesting budget exhausted" stmt.span
  | n + 1, stmt => do
    match stmt with
    | .return_ value span =>
      let result := s!"#returned:{span.start}"
      return .block [.let_ false result none value span,
        .return_ (.array [.var result span, tuple loans span] span) span] span
    | .block ss span => return .block (← ss.mapM (returns loans n)) span
    | .if_ guard a b span => return .if_ guard (← returns loans n a) (← returns loans n b) span
    | .for_ init guard update body span => return .for_ init guard update (← returns loans n body) span
    | .while_ guard body span => return .while_ guard (← returns loans n body) span
    | .forOf mutable name collection body span => return .forOf mutable name collection (← returns loans n body) span
    | .switch_ value cases span =>
      return .switch_ value (← cases.mapM fun (label, ss) => do return (label, ← ss.mapM (returns loans n))) span
    | .measured measure body span => return .measured measure (← returns loans n body) span
    | _ => return stmt

end Ariadne.Shallow.StatePlan
