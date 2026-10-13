import Ariadne.StatementConvergence
import Ariadne.CallConvergence
import Ariadne.Shallow.Adequacy.Function
import Ariadne.Shallow.Adequacy.MapExpressions
import Ariadne.Shallow.Adequacy.ClassMutation

/-!
Weakest preconditions over the original evaluator. Each rule matches one
syntactic form and states what must hold of its operands' results, so a proof
about a concrete source body proceeds by applying one rule per node. The
predicates are budget-free: every rule is derived from convergence of the
existing fuel-indexed evaluator.
-/

namespace Ariadne

def WPE (program : Program) (state : State) (expression : Expr) (post : Value → State → Prop) : Prop :=
  ∃ value after, Evaluates program state expression value after ∧ post value after

def WPA (program : Program) (state : State) (expressions : List Expr)
    (post : List Value → State → Prop) : Prop :=
  ∃ values after, EvaluatesArgs program state expressions values after ∧ post values after

def WPI (program : Program) (state : State) (target : Value) (args : List Value)
    (post : Value → State → Prop) : Prop :=
  ∃ value after, Invokes program state target args value after ∧ post value after

def WPS (program : Program) (state : State) (statement : Stmt) (post : Completion → Prop) : Prop :=
  ∃ out, ExecutesStatement program state statement out ∧ post out

def WPB (program : Program) (state : State) (statements : List Stmt) (post : Completion → Prop) : Prop :=
  ∃ out, ExecutesBlock program state statements out ∧ post out

def WPEach (program : Program) (state : State) (name : String) (body : Stmt) (values : List Value)
    (post : Completion → Prop) : Prop :=
  ∃ out, Converges (fun fuel => eachBody program fuel state name body values) (.ok out) ∧ post out

def WPLoop (program : Program) (state : State) (guard : Expr) (body : Stmt) (update : Option Stmt)
    (post : Completion → Prop) : Prop :=
  ∃ out, Converges (fun fuel => loop program fuel state guard body update) (.ok out) ∧ post out

def WPTraverse (program : Program) (state : State) (callback : Value) (values : List Value)
    (index : Nat) (mode : String) (post : List Value → State → Prop) : Prop :=
  ∃ results after, Converges (fun fuel => traverse program fuel state callback values index mode)
    (.ok (results, after)) ∧ post results after

/-- Switch case selection only evaluates literal labels, so it never changes the state. -/
def SelectsCase (program : Program) (state : State) (value : Value)
    (cases : List (Option Expr × List Stmt)) (selected : Option Nat) : Prop :=
  Converges (fun fuel => selectCase program fuel state value cases 0 none) (.ok selected)

/-- A switch absorbs its own `break` and restores the enclosing bindings. -/
def Completion.leaveSwitch (out : Completion) (env : Env) : Completion :=
  { out with control := if out.control == .broke then .normal else out.control, state := { out.state with env := env } }

private theorem controlBeq (a b : Control) : (a == b) = decide (a = b) := by cases a <;> cases b <;> rfl

theorem WPE.mono {program : Program} {state : State} {expression : Expr} {p q : Value → State → Prop}
    (h : WPE program state expression p) (f : ∀ v s, p v s → q v s) : WPE program state expression q := by
  obtain ⟨v, s, e, hp⟩ := h
  exact ⟨v, s, e, f v s hp⟩

theorem WPS.mono {program : Program} {state : State} {statement : Stmt} {p q : Completion → Prop}
    (h : WPS program state statement p) (f : ∀ out, p out → q out) : WPS program state statement q := by
  obtain ⟨out, e, hp⟩ := h
  exact ⟨out, e, f out hp⟩

theorem WPB.mono {program : Program} {state : State} {statements : List Stmt} {p q : Completion → Prop}
    (h : WPB program state statements p) (f : ∀ out, p out → q out) : WPB program state statements q := by
  obtain ⟨out, e, hp⟩ := h
  exact ⟨out, e, f out hp⟩

theorem WPI.mono {program : Program} {state : State} {target : Value} {args : List Value}
    {p q : Value → State → Prop} (h : WPI program state target args p) (f : ∀ v s, p v s → q v s) :
    WPI program state target args q := by
  obtain ⟨v, s, e, hp⟩ := h
  exact ⟨v, s, e, f v s hp⟩

/-! ## Expressions -/

theorem WPE.literal {program : Program} {state : State} {post : Value → State → Prop}
    {value : Literal} {span : Span} (h : post (Value.ofLiteral value) state) :
    WPE program state (.literal value span) post :=
  ⟨_, _, Evaluates.literal program state value span, h⟩

theorem WPE.var {program : Program} {state : State} {post : Value → State → Prop}
    {name : String} {span : Span} {value : Value}
    (lookup : state.lookup name = .ok value) (h : post value state) :
    WPE program state (.var name span) post :=
  ⟨value, state, Evaluates.variable program state name span value (State.lookup_present lookup) lookup, h⟩

theorem WPE.unary {program : Program} {state : State} {post : Value → State → Prop}
    {op : String} {arg : Expr} {span : Span}
    (h : WPE program state arg (fun v after => ∃ r, Ariadne.unary op v = .ok r ∧ post r after)) :
    WPE program state (.unary op arg span) post := by
  obtain ⟨v, after, e, r, hr, q⟩ := h
  exact ⟨r, after, e.unary op span hr, q⟩

theorem WPE.binary {program : Program} {state : State} {post : Value → State → Prop}
    {op : String} {left right : Expr} {span : Span}
    (strict : op ≠ "&&" ∧ op ≠ "||" ∧ op ≠ "??")
    (h : WPE program state left (fun a middle => WPE program middle right (fun b after =>
      ∃ r, Ariadne.binary op a b = .ok r ∧ post r after))) :
    WPE program state (.binary op left right span) post := by
  obtain ⟨a, middle, el, b, after, er, r, hr, q⟩ := h
  exact ⟨r, after, Evaluates.binary el er op span strict hr, q⟩

theorem WPE.and {program : Program} {state : State} {post : Value → State → Prop}
    {left right : Expr} {span : Span}
    (h : WPE program state left (fun a middle =>
      if a.truthy then WPE program middle right post else post a middle)) :
    WPE program state (.binary "&&" left right span) post := by
  obtain ⟨a, middle, el, h⟩ := h
  cases truth : a.truthy
  · simp only [truth] at h
    exact ⟨a, middle, Evaluates.and_false el truth span, by simpa using h⟩
  · simp only [truth, ↓reduceIte] at h
    obtain ⟨v, after, er, q⟩ := h
    exact ⟨v, after, Evaluates.and_true el er truth span, q⟩

theorem WPE.or {program : Program} {state : State} {post : Value → State → Prop}
    {left right : Expr} {span : Span}
    (h : WPE program state left (fun a middle =>
      if a.truthy then post a middle else WPE program middle right post)) :
    WPE program state (.binary "||" left right span) post := by
  obtain ⟨a, middle, el, h⟩ := h
  cases truth : a.truthy
  · simp only [truth] at h
    obtain ⟨v, after, er, q⟩ := by simpa using h
    exact ⟨v, after, Evaluates.or_false el er truth span, q⟩
  · simp only [truth, ↓reduceIte] at h
    exact ⟨a, middle, Evaluates.or_true el truth span, h⟩

theorem WPE.coalesce {program : Program} {state : State} {post : Value → State → Prop}
    {left right : Expr} {span : Span}
    (h : WPE program state left (fun a middle =>
      if a = .undefined ∨ a = .null then WPE program middle right post else post a middle)) :
    WPE program state (.binary "??" left right span) post := by
  obtain ⟨a, middle, el, h⟩ := h
  by_cases missing : a = .undefined ∨ a = .null
  · simp only [missing, ↓reduceIte] at h
    obtain ⟨v, after, er, q⟩ := h
    exact ⟨v, after, Evaluates.coalesce_nullish el er span missing, q⟩
  · simp only [missing, ↓reduceIte] at h
    exact ⟨a, middle, Evaluates.coalesce_defined el right span
      ⟨fun same => missing (Or.inl same), fun same => missing (Or.inr same)⟩, h⟩

theorem WPE.conditional {program : Program} {state : State} {post : Value → State → Prop}
    {condition yes no : Expr} {span : Span}
    (h : WPE program state condition (fun test middle =>
      WPE program middle (if test.truthy then yes else no) post)) :
    WPE program state (.conditional condition yes no span) post := by
  obtain ⟨test, middle, ec, v, after, eb, q⟩ := h
  exact ⟨v, after, Evaluates.conditional ec eb span, q⟩

theorem WPE.member {program : Program} {state : State} {post : Value → State → Prop}
    {receiver : Expr} {field : String} {span : Span}
    (h : WPE program state receiver (fun a after => ∃ v, readMember after a field = .ok v ∧ post v after)) :
    WPE program state (.member receiver field span) post := by
  obtain ⟨a, after, e, v, hv, q⟩ := h
  exact ⟨v, after, e.member field span hv, q⟩

theorem WPE.index {program : Program} {state : State} {post : Value → State → Prop}
    {receiver index : Expr} {span : Span}
    (h : WPE program state receiver (fun a middle => WPE program middle index (fun i after =>
      ∃ v, readIndex after a i = .ok v ∧ post v after))) :
    WPE program state (.index receiver index span) post := by
  obtain ⟨a, middle, er, i, after, ei, v, hv, q⟩ := h
  exact ⟨v, after, Evaluates.index er ei span hv, q⟩

theorem WPE.call {program : Program} {state : State} {post : Value → State → Prop}
    {callee : Expr} {args : List Expr} {span : Span}
    (h : WPE program state callee (fun target selected =>
      WPA program selected args (fun values ready => WPI program ready target values post))) :
    WPE program state (.call callee args span) post := by
  obtain ⟨target, selected, ef, values, ready, ea, v, after, ei, q⟩ := h
  exact ⟨v, after, Evaluates.call ef ea ei span, q⟩

theorem WPE.lambda {program : Program} {state : State} {post : Value → State → Prop}
    {params : List Param} {body : Stmt} {span : Span}
    (h : post (.ref state.heap.length) (state.alloc (.closure params body state.env)).2) :
    WPE program state (.lambda params body span) post :=
  ⟨_, _, ⟨(by intro h; cases h), 1, rfl⟩, h⟩

theorem WPE.newMap {program : Program} {state : State} {post : Value → State → Prop}
    {key value : Ty} {span : Span}
    (h : post (.ref state.heap.length) (state.alloc (.map [])).2) :
    WPE program state (.newMap key value span) post :=
  ⟨_, _, ⟨(by intro h; cases h), 1, rfl⟩, h⟩

theorem WPA.nil {program : Program} {state : State} {post : List Value → State → Prop}
    (h : post [] state) : WPA program state [] post :=
  ⟨[], state, EvaluatesArgs.nil program state, h⟩

theorem WPA.cons {program : Program} {state : State} {post : List Value → State → Prop}
    {expression : Expr} {rest : List Expr}
    (h : WPE program state expression (fun v middle =>
      WPA program middle rest (fun vs after => post (v :: vs) after))) :
    WPA program state (expression :: rest) post := by
  obtain ⟨v, middle, e, vs, after, es, q⟩ := h
  exact ⟨v :: vs, after, EvaluatesArgs.cons e es, q⟩

/-! ## Array literals, including spread elements -/

def EvaluatesElements (program : Program) (before : State) (elements : List Expr)
    (values : List Value) (after : State) : Prop :=
  Converges (fun fuel => evalElements program fuel before elements) (.ok (values, after))

theorem EvaluatesElements.eventually {program : Program} {before after : State}
    {elements : List Expr} {values : List Value} (h : EvaluatesElements program before elements values after) :
    ∃ threshold, ∀ fuel, threshold ≤ fuel → evalElements program fuel before elements = .ok (values, after) :=
  ((converges_iff_eventually _ (fun h => evalElements_fuel_mono program h before elements) _).mp h).2

def WPElements (program : Program) (state : State) (elements : List Expr)
    (post : List Value → State → Prop) : Prop :=
  ∃ values after, EvaluatesElements program state elements values after ∧ post values after

theorem WPElements.nil {program : Program} {state : State} {post : List Value → State → Prop}
    (h : post [] state) : WPElements program state [] post :=
  ⟨[], state, ⟨(by intro h; cases h), 1, rfl⟩, h⟩

theorem WPElements.spread {program : Program} {state : State} {post : List Value → State → Prop}
    {source : Expr} {span : Span} {rest : List Expr}
    (h : WPE program state source (fun v middle => ∃ xs spread, iterable middle v = .ok (xs, spread) ∧
      WPElements program spread rest (fun ys after => post (xs ++ ys) after))) :
    WPElements program state (.spread source span :: rest) post := by
  obtain ⟨v, middle, e, xs, spread, iterated, ys, after, es, q⟩ := h
  obtain ⟨ne, he⟩ := e.eventually
  obtain ⟨nr, hr⟩ := es.eventually
  refine ⟨xs ++ ys, after, ⟨(by intro h; cases h), max ne nr + 1, ?_⟩, q⟩
  simp [evalElements, he _ (Nat.le_max_left ..), hr _ (Nat.le_max_right ..), iterated,
    bind, Except.bind, pure, Except.pure]

theorem WPElements.single {program : Program} {state : State} {post : List Value → State → Prop}
    {element : Expr} {rest : List Expr} (plain : ∀ source span, element ≠ .spread source span)
    (h : WPE program state element (fun v middle =>
      WPElements program middle rest (fun ys after => post (v :: ys) after))) :
    WPElements program state (element :: rest) post := by
  obtain ⟨v, middle, e, ys, after, es, q⟩ := h
  obtain ⟨ne, he⟩ := e.eventually
  obtain ⟨nr, hr⟩ := es.eventually
  refine ⟨v :: ys, after, ⟨(by intro h; cases h), max ne nr + 1, ?_⟩, q⟩
  cases element
  case spread source span => exact absurd rfl (plain source span)
  all_goals simp [evalElements, he _ (Nat.le_max_left ..), hr _ (Nat.le_max_right ..),
    bind, Except.bind, pure, Except.pure]

theorem WPE.array {program : Program} {state : State} {post : Value → State → Prop}
    {elements : List Expr} {span : Span}
    (h : WPElements program state elements (fun xs after => xs.length < 4294967296 ∧
      post (.ref after.heap.length) (after.alloc (.array xs)).2)) :
    WPE program state (.array elements span) post := by
  obtain ⟨xs, after, e, bound, q⟩ := h
  obtain ⟨_, fuel, evaluated⟩ := e
  refine ⟨_, _, ⟨(by intro h; cases h), fuel + 1, ?_⟩, q⟩
  have small : ¬ xs.length ≥ 4294967296 := by omega
  simp [evalExpr, evaluated, small, State.alloc, bind, Except.bind, pure, Except.pure]

/-! ## Invocations -/

theorem WPI.map_get {program : Program} {state : State} {post : Value → State → Prop}
    {address : Nat} {entries : List (Value × Value)} {key : Value}
    (lookup : state.heap[address]? = some (.map entries)) (h : post (mapGet entries key) state) :
    WPI program state (.method address "get") [key] post :=
  ⟨_, _, ⟨(by intro h; cases h), 1, by simp [apply, lookup, pure, Except.pure]⟩, h⟩

theorem WPI.map_has {program : Program} {state : State} {post : Value → State → Prop}
    {address : Nat} {entries : List (Value × Value)} {key : Value}
    (lookup : state.heap[address]? = some (.map entries)) (h : post (.boolean (mapHas entries key)) state) :
    WPI program state (.method address "has") [key] post :=
  ⟨_, _, ⟨(by intro h; cases h), 1, by simp [apply, lookup, pure, Except.pure]⟩, h⟩

theorem WPI.map_set {program : Program} {state : State} {post : Value → State → Prop}
    {address : Nat} {entries : List (Value × Value)} {key value : Value}
    (lookup : state.heap[address]? = some (.map entries))
    (h : post (.ref address) { state with heap := state.heap.set address (.map (mapSet entries key value)) }) :
    WPI program state (.method address "set") [key, value] post := by
  have bound : address < state.heap.length := (List.getElem?_eq_some_iff.mp lookup).choose
  refine ⟨_, _, ⟨(by intro h; cases h), 1, ?_⟩, h⟩
  simp only [apply, lookup]
  simp [State.write, bound, bind, Except.bind, pure, Except.pure]

theorem WPI.map_delete {program : Program} {state : State} {post : Value → State → Prop}
    {address : Nat} {entries : List (Value × Value)} {key : Value}
    (lookup : state.heap[address]? = some (.map entries))
    (h : post (.boolean (mapHas entries key))
      { state with heap := state.heap.set address (.map (mapDelete entries key)) }) :
    WPI program state (.method address "delete") [key] post := by
  have bound : address < state.heap.length := (List.getElem?_eq_some_iff.mp lookup).choose
  refine ⟨_, _, ⟨(by intro h; cases h), 1, ?_⟩, h⟩
  simp only [apply, lookup]
  simp [State.write, bound, bind, Except.bind, pure, Except.pure]

theorem WPI.array_slice {program : Program} {state : State} {post : Value → State → Prop}
    {address : Nat} {values : List Value}
    (lookup : state.heap[address]? = some (.array values))
    (h : post (.ref state.heap.length) (state.alloc (.array values)).2) :
    WPI program state (.method address "slice") [] post :=
  ⟨_, _, ⟨(by intro h; cases h), 1, by simp [apply, lookup, State.alloc, pure, Except.pure]⟩, h⟩

theorem WPI.array_filter {program : Program} {state : State} {post : Value → State → Prop}
    {address : Nat} {values : List Value} {callback : Value}
    (lookup : state.heap[address]? = some (.array values))
    (h : WPTraverse program state callback values 0 "filter" (fun results after =>
      post (.ref after.heap.length) (after.alloc (.array results)).2)) :
    WPI program state (.method address "filter") [callback] post := by
  obtain ⟨results, after, ⟨_, fuel, traversed⟩, q⟩ := h
  refine ⟨_, _, ⟨(by intro h; cases h), fuel + 1, ?_⟩, q⟩
  simp [apply, lookup, traversed, State.alloc, bind, Except.bind, pure, Except.pure]

/-- Invoke an actual class method; the body runs in a fresh call frame and the
caller's lexical bindings are restored. -/
theorem WPI.method {program : Program} {state : State} {post : Value → State → Prop}
    {class_ : Class} {method : Ariadne.Function} {address : Nat}
    {fields : List (String × Value)} {args : List Value}
    (receiver : state.heap[address]? = some (.instance_ class_.name fields))
    (classLookup : program.classes.find? (·.name == class_.name) = some class_)
    (methodLookup : class_.methods.find? (·.name == method.name) = some method)
    (h : WPS program (Shallow.Adequacy.bindArguments state
        ({name := "this", ty := .class_ class_.name} :: method.params) (.ref address :: args))
      method.body (fun out => (out.control = .normal ∨ out.control = .returned) ∧
        post out.value { out.state with env := state.env })) :
    WPI program state (.method address method.name) args post := by
  obtain ⟨out, body, normal, q⟩ := h
  exact ⟨_, _, invoke_method_completion receiver classLookup methodLookup body normal, q⟩

/-- Apply a closure; its parameters are bound over the captured environment. -/
theorem WPI.closure {program : Program} {state : State} {post : Value → State → Prop}
    {address : Nat} {params : List Param} {body : Stmt} {captured : Env} {args : List Value}
    (lookup : state.heap[address]? = some (.closure params body captured))
    (h : WPS program ((params.zip args).foldl (fun s (p, v) => s.declare p.name v) { state with env := captured })
      body (fun out => (out.control = .normal ∨ out.control = .returned) ∧
        post out.value { out.state with env := state.env })) :
    WPI program state (.ref address) args post := by
  obtain ⟨out, ⟨_, fuel, executed⟩, normal, q⟩ := h
  refine ⟨_, _, ⟨(by intro h; cases h), fuel + 2, ?_⟩, q⟩
  dsimp only at executed
  simp only [apply, lookup, callBody]
  change (exec program fuel _ body).bind (fun result =>
    if result.control == Control.broke || result.control == Control.continued then
      .error (Fault.invariant "loop control escaped a function")
    else .ok (result.value, {result.state with env := state.env})) = _
  rw [executed]
  rcases normal with normal | normal <;> simp [normal, Except.bind] <;> decide

/-- Call a named source function in a fresh frame; the caller's bindings are restored. -/
theorem WPI.function {program : Program} {state : State} {post : Value → State → Prop}
    {function : Ariadne.Function} {args : List Value}
    (lookup : program.functions.find? (fun f => f.name == function.name) = some function)
    (h : WPS program (Shallow.Adequacy.bindArguments state function.params args) function.body
      (fun out => (out.control = .normal ∨ out.control = .returned) ∧
        post out.value { out.state with env := state.env })) :
    WPI program state (.function function.name) args post := by
  obtain ⟨out, ⟨_, fuel, executed⟩, normal, q⟩ := h
  refine ⟨_, _, ⟨(by intro h; cases h), fuel + 2, ?_⟩, q⟩
  dsimp only at executed
  simp only [apply, lookup, callBody]
  change (exec program fuel (Shallow.Adequacy.bindArguments state function.params args) function.body).bind
    (fun result => if result.control == Control.broke || result.control == Control.continued then
      .error (Fault.invariant "loop control escaped a function")
    else .ok (result.value, {result.state with env := state.env})) = _
  rw [executed]
  rcases normal with normal | normal <;> simp [normal, Except.bind] <;> decide

theorem WPTraverse.nil {program : Program} {state : State} {callback : Value} {index : Nat} {mode : String}
    {post : List Value → State → Prop} (h : post [] state) :
    WPTraverse program state callback [] index mode post :=
  ⟨[], state, ⟨(by intro h; cases h), 1, by simp [traverse, pure, Except.pure]⟩, h⟩

theorem WPTraverse.cons {program : Program} {state : State} {callback : Value} {index : Nat}
    {mode : String} {x : Value} {xs : List Value} {post : List Value → State → Prop}
    (h : WPI program state callback [x, .number (Float.Model.ofNat index)] (fun y middle =>
      WPTraverse program middle callback xs (index + 1) mode (fun ys after =>
        post (if mode == "filter" then (if y.truthy then x :: ys else ys) else y :: ys) after))) :
    WPTraverse program state callback (x :: xs) index mode post := by
  obtain ⟨y, middle, ⟨_, ni, invoked⟩, ys, after, ⟨_, nt, traversed⟩, q⟩ := h
  have hi := ((converges_iff_eventually _ (fun h => apply_fuel_mono program h state callback _) _).mp
    ⟨(by intro h; cases h), ni, invoked⟩).2
  have ht := ((converges_iff_eventually _
    (fun h => traverse_fuel_mono program h middle callback xs (index + 1) mode) _).mp
    ⟨(by intro h; cases h), nt, traversed⟩).2
  obtain ⟨ti, hi⟩ := hi
  obtain ⟨tt, ht⟩ := ht
  refine ⟨_, after, ⟨(by intro h; cases h), max ti tt + 1, ?_⟩, q⟩
  simp [traverse, hi _ (Nat.le_max_left ..), ht _ (Nat.le_max_right ..), bind, Except.bind, pure, Except.pure]

/-! ## Statements -/

theorem WPS.let_ {program : Program} {state : State} {post : Completion → Prop}
    {mutable : Bool} {name : String} {annotation : Option Ty} {value : Expr} {span : Span}
    (h : WPE program state value (fun v after => post { state := after.declare name v })) :
    WPS program state (.let_ mutable name annotation value span) post := by
  obtain ⟨v, after, e, q⟩ := h
  exact ⟨_, ExecutesStatement.let_ e mutable name annotation span, q⟩

theorem WPS.expr {program : Program} {state : State} {post : Completion → Prop}
    {value : Expr} {span : Span}
    (h : WPE program state value (fun _ after => post { state := after })) :
    WPS program state (.expr value span) post := by
  obtain ⟨v, after, e, q⟩ := h
  obtain ⟨_, fuel, evaluated⟩ := e
  exact ⟨_, ⟨(by intro h; cases h), fuel + 1, by simp [exec, evaluated, bind, Except.bind, pure, Except.pure]⟩, q⟩

theorem WPS.assignVar {program : Program} {state : State} {post : Completion → Prop}
    {name : String} {targetSpan : Span} {value : Expr} {span : Span}
    (h : WPE program state value (fun v middle => ∃ after, middle.assign name v = .ok after ∧
      post { state := after })) :
    WPS program state (.assign (.var name targetSpan) value span) post := by
  obtain ⟨v, middle, e, after, assigned, q⟩ := h
  obtain ⟨_, fuel, evaluated⟩ := e
  exact ⟨_, ⟨(by intro h; cases h), fuel + 2, by
    simp [exec, assignTarget, evaluated, assigned, bind, Except.bind, pure, Except.pure]⟩, q⟩

theorem WPS.return_ {program : Program} {state : State} {post : Completion → Prop}
    {value : Expr} {span : Span}
    (h : WPE program state value (fun v after => post { control := .returned, value := v, state := after })) :
    WPS program state (.return_ value span) post := by
  obtain ⟨v, after, e, q⟩ := h
  exact ⟨_, ExecutesStatement.return_ e span, q⟩

theorem WPS.if_ {program : Program} {state : State} {post : Completion → Prop}
    {condition : Expr} {yes no : Stmt} {span : Span}
    (h : WPE program state condition (fun test middle =>
      WPS program middle (if test.truthy then yes else no) post)) :
    WPS program state (.if_ condition yes no span) post := by
  obtain ⟨test, middle, e, out, branch, q⟩ := h
  exact ⟨out, ExecutesStatement.if_ e branch span, q⟩

theorem WPS.block {program : Program} {state : State} {post : Completion → Prop}
    {statements : List Stmt} {span : Span}
    (h : WPB program state statements (fun out => post { out with state := { out.state with env := state.env } })) :
    WPS program state (.block statements span) post := by
  obtain ⟨out, body, q⟩ := h
  exact ⟨_, ExecutesStatement.block body span, q⟩

theorem WPS.break_ {program : Program} {state : State} {post : Completion → Prop} {span : Span}
    (h : post { control := .broke, state }) : WPS program state (.break_ span) post :=
  ⟨_, ⟨(by intro h; cases h), 1, rfl⟩, h⟩

theorem WPS.continue_ {program : Program} {state : State} {post : Completion → Prop} {span : Span}
    (h : post { control := .continued, state }) : WPS program state (.continue_ span) post :=
  ⟨_, ⟨(by intro h; cases h), 1, rfl⟩, h⟩

theorem WPB.nil {program : Program} {state : State} {post : Completion → Prop}
    (h : post { state }) : WPB program state [] post :=
  ⟨_, ExecutesBlock.nil program state, h⟩

theorem WPB.cons {program : Program} {state : State} {post : Completion → Prop}
    {statement : Stmt} {rest : List Stmt}
    (h : WPS program state statement (fun out =>
      if out.control = .normal then WPB program out.state rest post else post out)) :
    WPB program state (statement :: rest) post := by
  obtain ⟨out, head, q⟩ := h
  by_cases normal : out.control = .normal
  · simp only [normal, ↓reduceIte] at q
    obtain ⟨final, tail, q⟩ := q
    exact ⟨final, ExecutesBlock.next head normal tail, q⟩
  · simp only [normal, ↓reduceIte] at q
    exact ⟨out, ExecutesBlock.stop head rest normal, q⟩

theorem WPS.forOf {program : Program} {state : State} {post : Completion → Prop}
    {mutable : Bool} {name : String} {collection : Expr} {body : Stmt} {span : Span}
    (h : WPE program state collection (fun value middle => ∃ xs ready,
      iterable middle value = .ok (xs, ready) ∧ WPEach program ready name body xs post)) :
    WPS program state (.forOf mutable name collection body span) post := by
  obtain ⟨value, middle, e, xs, ready, iterated, out, ⟨_, ne, each⟩, q⟩ := h
  obtain ⟨nc, hc⟩ := e.eventually
  have he := ((converges_iff_eventually _ (fun h => eachBody_fuel_mono program h ready name body xs) _).mp
    ⟨(by intro h; cases h), ne, each⟩).2
  obtain ⟨te, he⟩ := he
  refine ⟨out, ⟨(by intro h; cases h), max nc te + 1, ?_⟩, q⟩
  simp [exec, hc _ (Nat.le_max_left ..), iterated, he _ (Nat.le_max_right ..), bind, Except.bind]

theorem WPEach.nil {program : Program} {state : State} {name : String} {body : Stmt}
    {post : Completion → Prop} (h : post { state }) : WPEach program state name body [] post :=
  ⟨_, ⟨(by intro h; cases h), 1, rfl⟩, h⟩

theorem WPEach.cons {program : Program} {state : State} {name : String} {body : Stmt}
    {x : Value} {xs : List Value} {post : Completion → Prop}
    (h : WPS program (state.declare name x) body (fun out =>
      if out.control = .returned then post { out with state := { out.state with env := state.env } }
      else if out.control = .broke then post { state := { out.state with env := state.env } }
      else WPEach program { out.state with env := state.env } name body xs post)) :
    WPEach program state name body (x :: xs) post := by
  obtain ⟨out, ⟨_, nb, executed⟩, q⟩ := h
  have hb := ((converges_iff_eventually _ (fun h => exec_fuel_mono program h (state.declare name x) body) _).mp
    ⟨(by intro h; cases h), nb, executed⟩).2
  obtain ⟨tb, hb⟩ := hb
  by_cases returned : out.control = .returned
  · simp only [returned, ↓reduceIte] at q
    refine ⟨_, ⟨(by intro h; cases h), tb + 1, ?_⟩, q⟩
    simp [eachBody, hb _ (Nat.le_refl _), returned, bind, Except.bind, pure, Except.pure, controlBeq]
  · by_cases broke : out.control = .broke
    · simp only [returned, broke, ↓reduceIte] at q
      refine ⟨_, ⟨(by intro h; cases h), tb + 1, ?_⟩, q⟩
      simp [eachBody, hb _ (Nat.le_refl _), broke, bind, Except.bind, pure, Except.pure, controlBeq]
    · simp only [returned, broke, ↓reduceIte] at q
      obtain ⟨final, ⟨_, nr, rest⟩, q⟩ := q
      have hr := ((converges_iff_eventually _
        (fun h => eachBody_fuel_mono program h { out.state with env := state.env } name body xs) _).mp
        ⟨(by intro h; cases h), nr, rest⟩).2
      obtain ⟨tr, hr⟩ := hr
      refine ⟨final, ⟨(by intro h; cases h), max tb tr + 1, ?_⟩, q⟩
      simp [eachBody, hb _ (Nat.le_max_left ..), returned, broke, hr _ (Nat.le_max_right ..),
        bind, Except.bind, pure, Except.pure, controlBeq]

theorem WPS.for_ {program : Program} {state : State} {post : Completion → Prop}
    {init : Stmt} {guard : Expr} {update body : Stmt} {span : Span}
    (h : WPS program state init (fun initial => WPLoop program initial.state guard body (some update)
      (fun out => post { out with state := { out.state with env := state.env } }))) :
    WPS program state (.for_ init guard update body span) post := by
  obtain ⟨initial, ei, out, ⟨_, nl, looped⟩, q⟩ := h
  obtain ⟨ni, hi⟩ := ei.eventually
  have hl := ((converges_iff_eventually _
    (fun h => loop_fuel_mono program h initial.state guard body (some update)) _).mp
    ⟨(by intro h; cases h), nl, looped⟩).2
  obtain ⟨tl, hl⟩ := hl
  refine ⟨_, ⟨(by intro h; cases h), max ni tl + 1, ?_⟩, q⟩
  simp [exec, hi _ (Nat.le_max_left ..), hl _ (Nat.le_max_right ..), bind, Except.bind, pure, Except.pure]

theorem WPLoop.step {program : Program} {state : State} {guard : Expr} {body update : Stmt}
    {post : Completion → Prop}
    (h : WPE program state guard (fun test middle =>
      if test.truthy then WPS program middle body (fun out =>
        if out.control = .returned then post out
        else if out.control = .broke then post { state := out.state }
        else WPS program out.state update (fun updated =>
          WPLoop program updated.state guard body (some update) post))
      else post { state := middle })) :
    WPLoop program state guard body (some update) post := by
  obtain ⟨test, middle, eg, h⟩ := h
  obtain ⟨ng, hg⟩ := eg.eventually
  cases truth : test.truthy
  · simp only [truth] at h
    refine ⟨_, ⟨(by intro h; cases h), ng + 1, ?_⟩, by simpa using h⟩
    simp [loop, hg _ (Nat.le_refl _), truth, bind, Except.bind, pure, Except.pure]
  · simp only [truth, ↓reduceIte] at h
    obtain ⟨out, eb, q⟩ := h
    obtain ⟨nb, hb⟩ := eb.eventually
    by_cases returned : out.control = .returned
    · simp only [returned, ↓reduceIte] at q
      refine ⟨_, ⟨(by intro h; cases h), max ng nb + 1, ?_⟩, q⟩
      simp [loop, hg _ (Nat.le_max_left ..), truth, hb _ (Nat.le_max_right ..), returned,
        bind, Except.bind, pure, Except.pure, controlBeq]
    · by_cases broke : out.control = .broke
      · simp only [returned, broke, ↓reduceIte] at q
        refine ⟨_, ⟨(by intro h; cases h), max ng nb + 1, ?_⟩, q⟩
        simp [loop, hg _ (Nat.le_max_left ..), truth, hb _ (Nat.le_max_right ..), broke,
          bind, Except.bind, pure, Except.pure, controlBeq]
      · simp only [returned, broke, ↓reduceIte] at q
        obtain ⟨updated, eu, final, ⟨_, nl, looped⟩, q⟩ := q
        obtain ⟨nu, hu⟩ := eu.eventually
        have hl := ((converges_iff_eventually _
          (fun h => loop_fuel_mono program h updated.state guard body (some update)) _).mp
          ⟨(by intro h; cases h), nl, looped⟩).2
        obtain ⟨tl, hl⟩ := hl
        let n := max ng (max nb (max nu tl))
        have hg' := hg n (Nat.le_max_left ..)
        have hb' := hb n (Nat.le_trans (Nat.le_max_left ..) (Nat.le_max_right ..))
        have hu' := hu n (Nat.le_trans (Nat.le_trans (Nat.le_max_left ..) (Nat.le_max_right ..)) (Nat.le_max_right ..))
        have hl' := hl n (Nat.le_trans (Nat.le_trans (Nat.le_max_right ..) (Nat.le_max_right ..)) (Nat.le_max_right ..))
        refine ⟨final, ⟨(by intro h; cases h), n + 1, ?_⟩, q⟩
        simp [loop, hg', truth, hb', returned, broke, hu', hl', bind, Except.bind, pure, Except.pure,
          controlBeq, Except.map]

theorem WPS.switch_ {program : Program} {state : State} {post : Completion → Prop}
    {value : Expr} {cases : List (Option Expr × List Stmt)} {span : Span}
    (h : WPE program state value (fun v middle => ∃ selected, SelectsCase program middle v cases selected ∧
      match selected with
      | none => post { state := middle }
      | some index => WPB program middle ((cases.drop index).flatMap Prod.snd) (fun out =>
          post (out.leaveSwitch middle.env)))) :
    WPS program state (.switch_ value cases span) post := by
  obtain ⟨v, middle, ev, selected, ⟨_, ns, sel⟩, h⟩ := h
  obtain ⟨nv, hv⟩ := ev.eventually
  have hs := ((converges_iff_eventually _
    (fun h => selectCase_fuel_mono program h middle v cases 0 none) _).mp
    ⟨(by intro h; cases h), ns, sel⟩).2
  obtain ⟨ts, hs⟩ := hs
  cases selected with
  | none =>
    refine ⟨_, ⟨(by intro h; cases h), max nv ts + 1, ?_⟩, h⟩
    simp [exec, hv _ (Nat.le_max_left ..), hs _ (Nat.le_max_right ..), bind, Except.bind, pure, Except.pure]
  | some index =>
    obtain ⟨out, eb, q⟩ := h
    obtain ⟨nb, hb⟩ := eb.eventually
    let n := max nv (max ts nb)
    refine ⟨_, ⟨(by intro h; cases h), n + 1, ?_⟩, q⟩
    simp [exec, hv n (Nat.le_max_left ..),
      hs n (Nat.le_trans (Nat.le_max_left ..) (Nat.le_max_right ..)),
      hb n (Nat.le_trans (Nat.le_max_right ..) (Nat.le_max_right ..)), bind, Except.bind, pure, Except.pure,
      Completion.leaveSwitch]

/-- Case selection when every label is a literal or `default`, as the checker requires. -/
def literalCase (value : Value) : List (Option Expr × List Stmt) → Nat → Option Nat → Option Nat
  | [], _, fallback => fallback
  | (none, _) :: cases, index, _ => literalCase value cases (index + 1) (some index)
  | (some (.literal label _), _) :: cases, index, fallback =>
    if strictEqual value (Value.ofLiteral label) then some index
    else literalCase value cases (index + 1) fallback
  | (some _, _) :: cases, index, fallback => literalCase value cases (index + 1) fallback

def literalLabels : List (Option Expr × List Stmt) → Bool
  | [] => true
  | (none, _) :: cases => literalLabels cases
  | (some (.literal _ _), _) :: cases => literalLabels cases
  | (some _, _) :: _ => false

theorem selectCase_literals (program : Program) (state : State) (value : Value) :
    ∀ (cases : List (Option Expr × List Stmt)) (index : Nat) (fallback : Option Nat),
      literalLabels cases = true →
      selectCase program (cases.length + 2) state value cases index fallback =
        .ok (literalCase value cases index fallback)
  | [], _, _, _ => rfl
  | (none, _) :: cases, index, _, labels => by
    simp only [selectCase, List.length_cons]
    rw [show cases.length + 1 + 1 = cases.length + 2 from rfl]
    exact selectCase_literals program state value cases _ _ labels
  | (some (.literal label span), _) :: cases, index, fallback, labels => by
    have rest := selectCase_literals program state value cases (index + 1) fallback labels
    simp only [selectCase, List.length_cons, literalCase]
    have evaluated : evalExpr program (cases.length + 1 + 1) state (.literal label span) =
        .ok (Value.ofLiteral label, state) := rfl
    simp only [evaluated, bind, Except.bind, pure, Except.pure]
    split
    · rfl
    · exact rest
  | (some (.var _ _), _) :: _, _, _, labels | (some (.unary _ _ _), _) :: _, _, _, labels
  | (some (.binary _ _ _ _), _) :: _, _, _, labels | (some (.conditional _ _ _ _), _) :: _, _, _, labels
  | (some (.call _ _ _), _) :: _, _, _, labels | (some (.member _ _ _), _) :: _, _, _, labels
  | (some (.index _ _ _), _) :: _, _, _, labels | (some (.array _ _), _) :: _, _, _, labels
  | (some (.record _ _), _) :: _, _, _, labels | (some (.lambda _ _ _), _) :: _, _, _, labels
  | (some (.newMap _ _ _), _) :: _, _, _, labels | (some (.newSet _ _), _) :: _, _, _, labels
  | (some (.newClass _ _ _), _) :: _, _, _, labels | (some (.spread _ _), _) :: _, _, _, labels => by
    simp [literalLabels] at labels

theorem SelectsCase.literals {program : Program} {state : State} {value : Value}
    {cases : List (Option Expr × List Stmt)} (labels : literalLabels cases = true) :
    SelectsCase program state value cases (literalCase value cases 0 none) :=
  ⟨(by intro h; cases h), _, selectCase_literals program state value cases 0 none labels⟩

theorem WPEach.mono {program : Program} {state : State} {name : String} {body : Stmt} {values : List Value}
    {p q : Completion → Prop} (h : WPEach program state name body values p) (f : ∀ out, p out → q out) :
    WPEach program state name body values q := by
  obtain ⟨out, e, hp⟩ := h
  exact ⟨out, e, f out hp⟩

theorem WPE.elim {program : Program} {state : State} {expression : Expr} {post : Value → State → Prop}
    (h : WPE program state expression post) : ∃ v after, Evaluates program state expression v after ∧ post v after := h
theorem WPI.elim {program : Program} {state : State} {target : Value} {args : List Value}
    {post : Value → State → Prop} (h : WPI program state target args post) :
    ∃ v after, Invokes program state target args v after ∧ post v after := h
theorem WPS.elim {program : Program} {state : State} {statement : Stmt} {post : Completion → Prop}
    (h : WPS program state statement post) : ∃ out, ExecutesStatement program state statement out ∧ post out := h
theorem WPB.elim {program : Program} {state : State} {statements : List Stmt} {post : Completion → Prop}
    (h : WPB program state statements post) : ∃ out, ExecutesBlock program state statements out ∧ post out := h

-- Clients prove these predicates only through the rules above, so automation
-- never unfolds one into its existential by accident.
attribute [irreducible] WPE WPA WPI WPS WPB WPEach WPLoop WPTraverse WPElements

end Ariadne
