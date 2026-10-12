import Ariadne.CompilerBase
import Ariadne.Calls

namespace Ariadne.Compile.Open

/-- Open code is proved against the source call interface and carries a causality
proof. Linking may replace that interface at any sufficiently large fuel prefix. -/
structure Fragment (p : Program) (α : Type) (meaning : Nat → α) where
  code : Target.Runtime → Nat → α
  correct : code (apply p) = meaning
  causal : Target.Causal code
  text : String

abbrev Expression (p : Program) (e : Expr) :=
  Fragment p (State → Result (Value × State)) (fun fuel s => evalExpr p fuel s e)
abbrev Arguments (p : Program) (es : List Expr) :=
  Fragment p (State → Result (List Value × State)) (fun fuel s => evalArgs p fuel s es)
abbrev Command (p : Program) (s : Stmt) :=
  Fragment p (State → Result Completion) (fun fuel state => exec p fuel state s)
abbrev Block (p : Program) (ss : List Stmt) :=
  Fragment p (State → Result Completion) (fun fuel state => execBlock p fuel state ss)

mutual
  /-- Compilation fuel is a frontend nesting limit, independent of runtime fuel. -/
  def expression (p : Program) (allowCalls : Bool) : (budget : Nat) → (e : Expr) → Checked (Expression p e)
    | 0, e => .error (exhausted e.span)
    | _ + 1, .literal v span => .ok {
        code := fun runtime => Target.literal v
        correct := by funext fuel s; cases fuel <;> rfl
        causal := fun _ _ _ _ => Target.Agree.refl _
        text := app "literal" [s!"({reprStr v})"] }
    | _ + 1, .var name span => .ok {
        code := fun runtime => Target.read name
        correct := by funext fuel s; cases fuel <;> rfl
        causal := fun _ _ _ _ => Target.Agree.refl _
        text := app "read" [reprStr name] }
    | n + 1, .unary op arg span => do
      let a ← expression p allowCalls n arg
      return {
        code := fun runtime => Target.unary op (a.code runtime)
        correct := by rw [a.correct]; funext fuel s; cases fuel <;> rfl
        causal := fun limit left right h => Target.unary_congr (a.causal limit left right h)
        text := app "unary" [reprStr op, a.text] }
    | n + 1, .binary op left right span => do
      let a ← expression p allowCalls n left
      let b ← expression p allowCalls n right
      return {
        code := fun runtime => Target.binary op (a.code runtime) (b.code runtime)
        correct := by rw [a.correct, b.correct]; funext fuel s; cases fuel <;> rfl
        causal := fun limit left right h => Target.binary_congr (a.causal limit left right h) (b.causal limit left right h)
        text := app "binary" [reprStr op, a.text, b.text] }
    | n + 1, .conditional guard yes no span => do
      let c ← expression p allowCalls n guard
      let a ← expression p allowCalls n yes
      let b ← expression p allowCalls n no
      return {
        code := fun runtime => Target.conditional (c.code runtime) (a.code runtime) (b.code runtime)
        correct := by
          rw [c.correct, a.correct, b.correct]
          funext fuel s
          cases fuel with
          | zero => rfl
          | succ n =>
            simp only [Target.conditional, evalExpr]
            congr 1
            funext pair
            split <;> rfl
        causal := fun limit left right h => Target.conditional_congr (c.causal limit left right h) (a.causal limit left right h) (b.causal limit left right h)
        text := app "conditional" [c.text, a.text, b.text] }
    | n + 1, .member object field span => do
      let a ← expression p allowCalls n object
      return {
        code := fun runtime => Target.member (a.code runtime) field
        correct := by rw [a.correct]; funext fuel s; cases fuel <;> rfl
        causal := fun limit left right h => Target.member_congr (a.causal limit left right h)
        text := app "member" [a.text, reprStr field] }
    | n + 1, .index object offset span => do
      let a ← expression p allowCalls n object
      let b ← expression p allowCalls n offset
      return {
        code := fun runtime => Target.index (a.code runtime) (b.code runtime)
        correct := by rw [a.correct, b.correct]; funext fuel s; cases fuel <;> rfl
        causal := fun limit left right h => Target.index_congr (a.causal limit left right h) (b.causal limit left right h)
        text := app "index" [a.text, b.text] }
    | n + 1, .call callee args span => do
      if !allowCalls then throw (unsupported span "function or method calls")
      let f ← expression p allowCalls n callee
      let a ← arguments p allowCalls n args
      return {
        code := fun runtime => Target.call runtime (f.code runtime) (a.code runtime)
        correct := by rw [f.correct, a.correct]; funext fuel s; cases fuel <;> rfl
        causal := fun limit left right h => Target.call_congr h
          (f.causal limit left right h) (a.causal limit left right h)
        text := app "call" ["_runtime", f.text, a.text] }
    | _ + 1, e@(.array ..) => .error (unsupported e.span "array allocation")
    | _ + 1, e@(.record ..) => .error (unsupported e.span "record allocation")
    | _ + 1, e@(.newMap ..) => .error (unsupported e.span "Map allocation")
    | _ + 1, e@(.lambda ..) => .error (unsupported e.span "callbacks")
  def arguments (p : Program) (allowCalls : Bool) : (budget : Nat) → (es : List Expr) → Checked (Arguments p es)
    | 0, es => .error (exhausted ((es.head?.map Expr.span).getD {}))
    | _ + 1, [] => .ok {
        code := fun _ => Target.noArgs
        correct := by funext fuel s; cases fuel <;> rfl
        causal := fun _ _ _ _ => Target.Agree.refl _
        text := "Target.noArgs" }
    | n + 1, first :: rest => do
      let a ← expression p allowCalls n first
      let b ← arguments p allowCalls n rest
      return {
        code := fun runtime => Target.consArg (a.code runtime) (b.code runtime)
        correct := by rw [a.correct, b.correct]; funext fuel s; cases fuel <;> rfl
        causal := fun limit left right h => Target.consArg_congr
          (a.causal limit left right h) (b.causal limit left right h)
        text := app "consArg" [a.text, b.text] }
end

mutual
  def statement (p : Program) (allowCalls : Bool) : (budget : Nat) → (s : Stmt) → Checked (Command p s)
    | 0, s => .error (exhausted s.span)
    | n + 1, .block ss span => do
      let b ← block p allowCalls n ss
      return {
        code := fun runtime => Target.scope (b.code runtime)
        correct := by rw [b.correct]; funext fuel s; cases fuel <;> rfl
        causal := fun limit left right h => Target.scope_congr (b.causal limit left right h)
        text := commandApp "scope" [b.text] }
    | n + 1, .let_ mutable name ty value span => do
      let v ← expression p allowCalls n value
      return {
        code := fun runtime => Target.declare name (v.code runtime)
        correct := by rw [v.correct]; funext fuel s; cases fuel <;> rfl
        causal := fun limit left right h => Target.declare_congr (v.causal limit left right h)
        text := commandApp "declare" [reprStr name, v.text] }
    | n + 1, .assign (.var name nameSpan) value span => do
      let v ← expression p allowCalls n value
      return {
        code := fun runtime => Target.assign name (v.code runtime)
        correct := by
          rw [v.correct]; funext fuel s
          cases fuel with
          | zero => rfl
          | succ n =>
            cases n with
            | zero => rfl
            | succ n =>
              cases h : evalExpr p n s value <;>
                simp [Target.assign, exec, assignTarget, h, bind, Except.bind]
        causal := fun limit left right h => Target.assign_congr (v.causal limit left right h)
        text := commandApp "assign" [reprStr name, v.text] }
    | _ + 1, .assign target _ _ => .error (unsupported target.span "writes through references")
    | n + 1, .expr value span => do
      let v ← expression p allowCalls n value
      return {
        code := fun runtime => Target.discard (v.code runtime)
        correct := by rw [v.correct]; funext fuel s; cases fuel <;> rfl
        causal := fun limit left right h => Target.discard_congr (v.causal limit left right h)
        text := commandApp "discard" [v.text] }
    | n + 1, .if_ guard yes no span => do
      let c ← expression p allowCalls n guard
      let a ← statement p allowCalls n yes
      let b ← statement p allowCalls n no
      return {
        code := fun runtime => Target.branch (c.code runtime) (a.code runtime) (b.code runtime)
        correct := by
          rw [c.correct, a.correct, b.correct]
          funext fuel s
          cases fuel with
          | zero => rfl
          | succ n =>
            simp only [Target.branch, exec]
            congr 1
            funext pair
            split <;> rfl
        causal := fun limit left right h => Target.branch_congr (c.causal limit left right h) (a.causal limit left right h) (b.causal limit left right h)
        text := commandApp "branch" [c.text, a.text, b.text] }
    | n + 1, .while_ guard body span => do
      let c ← expression p allowCalls n guard
      let b ← statement p allowCalls n body
      return {
        code := fun runtime => Target.while_ (c.code runtime) (b.code runtime)
        correct := by
          rw [c.correct, b.correct]
          funext fuel s
          cases fuel with
          | zero => rfl
          | succ n => exact congrFun (congrFun (Compile.loop_correct p guard body none) n) s
        causal := fun limit left right h => Target.while_congr (c.causal limit left right h) (b.causal limit left right h)
        text := commandApp "while_" [c.text, b.text] }
    | n + 1, .for_ init guard update body span => do
      let i ← statement p allowCalls n init
      let c ← expression p allowCalls n guard
      let u ← statement p allowCalls n update
      let b ← statement p allowCalls n body
      return {
        code := fun runtime => Target.for_ (i.code runtime) (c.code runtime) (u.code runtime) (b.code runtime)
        correct := by
          rw [i.correct, c.correct, u.correct, b.correct]
          funext fuel s
          cases fuel with
          | zero => rfl
          | succ n =>
            simp only [Target.for_, exec]
            have h := Compile.loop_correct p guard body (some update)
            simp only [Option.map] at h
            rw [h]
        causal := fun limit left right h => Target.for_congr (i.causal limit left right h) (c.causal limit left right h) (u.causal limit left right h) (b.causal limit left right h)
        text := commandApp "for_" [i.text, c.text, u.text, b.text] }
    | n + 1, .return_ value span => do
      let v ← expression p allowCalls n value
      return {
        code := fun runtime => Target.return_ (v.code runtime)
        correct := by rw [v.correct]; funext fuel s; cases fuel <;> rfl
        causal := fun limit left right h => Target.return_congr (v.causal limit left right h)
        text := commandApp "return_" [v.text] }
    | _ + 1, .break_ span => .ok {
        code := fun runtime => Target.break_
        correct := by funext fuel s; cases fuel <;> rfl
        causal := fun _ _ _ _ => Target.Agree.refl _
        text := "Target.break_" }
    | _ + 1, .continue_ span => .ok {
        code := fun runtime => Target.continue_
        correct := by funext fuel s; cases fuel <;> rfl
        causal := fun _ _ _ _ => Target.Agree.refl _
        text := "Target.continue_" }

  def block (p : Program) (allowCalls : Bool) : (budget : Nat) → (ss : List Stmt) → Checked (Block p ss)
    | 0, ss => .error (exhausted ((ss.head?.map Stmt.span).getD {}))
    | _ + 1, [] => .ok {
        code := fun runtime => Target.empty
        correct := by funext fuel s; cases fuel <;> rfl
        causal := fun _ _ _ _ => Target.Agree.refl _
        text := "Target.empty" }
    | n + 1, first :: rest => do
      let a ← statement p allowCalls n first
      let b ← block p allowCalls n rest
      return {
        code := fun runtime => Target.sequence (a.code runtime) (b.code runtime)
        correct := by rw [a.correct, b.correct]; funext fuel s; cases fuel <;> rfl
        causal := fun limit left right h => Target.sequence_congr (a.causal limit left right h) (b.causal limit left right h)
        text := commandApp "sequence" [a.text, b.text] }
end

end Ariadne.Compile.Open
