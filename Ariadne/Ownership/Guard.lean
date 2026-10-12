import Ariadne.Ownership.EntryPlan
import Ariadne.SourceFrom

namespace Ariadne.Ownership

def publicChildren (program : Program) : Object → Result (List Value)
  | .array values => .ok values
  | .map entries => .ok (entries.map Prod.snd)
  | .record fields => .ok (fields.map Prod.snd)
  | .set _ => .ok [] -- The checked dialect admits scalar elements only.
  | .instance_ name fields => do
    let some class_ := program.classes.find? (·.name == name)
      | .error (.typeError "entry guard encountered an undeclared class")
    return (fields.filter fun field => class_.fields.any
      (fun declared => declared.name == field.1 && !declared.private_)).map Prod.snd
  | _ => .error (.typeError "entry guard requires ordinary checked data objects")

def anyResult (query : α → Result Bool) : List α → Result Bool
  | [] => .ok false
  | value :: rest => do
    if ← query value then return true
    anyResult query rest

theorem anyResult_false_iff {query : α → Result Bool} {values : List α} :
    anyResult query values = .ok false ↔ ∀ value ∈ values, query value = .ok false := by
  induction values with
  | nil => simp [anyResult]
  | cons value rest ih =>
    cases checked : query value with
    | error error => simp [anyResult, checked, bind, Except.bind]
    | ok found => cases found <;> simp [anyResult, checked, ih, bind, Except.bind, pure, Except.pure]

/-- Search actual references, without evaluating user code or changing the
heap. The visited path handles sharing and cycles. The finite heap supplies
the bound; an invalid dangling reference fails before the implementation runs. -/
def containsReference (program : Program) (heap : Heap) (target : Nat) :
    Nat → List Nat → Value → Result Bool
  | fuel, visited, value => do
    let .ref address := value | return false
    if address == target then return true
    if visited.contains address then return false
    match fuel with
    | 0 => .error (.typeError "entry guard exceeded the allocated heap")
    | fuel + 1 =>
      let some object := heap[address]?
        | .error (.typeError "entry guard encountered a dangling reference")
      let children ← publicChildren program object
      anyResult (containsReference program heap target fuel (address :: visited)) children

private def rejectContained (program : Program) (heap : Heap) (target : Nat)
    (value : Value) : Result Unit := do
  if ← containsReference program heap target heap.length [] value then
    .error (.typeError "overlapping borrowed arguments")

private theorem rejectContained_iff {program : Program} {heap : Heap} {target : Nat}
    {value : Value} : rejectContained program heap target value = .ok () ↔
      containsReference program heap target heap.length [] value = .ok false := by
  unfold rejectContained
  cases searched : containsReference program heap target heap.length [] value with
  | error error => simp [bind, Except.bind]
  | ok found => cases found <;> simp [bind, Except.bind, pure, Except.pure]

private theorem unit_bind_iff (first second : Result Unit) :
    (first.bind fun _ => second) = .ok () ↔ first = .ok () ∧ second = .ok () := by
  cases first with
  | error error => simp [Except.bind]
  | ok result => cases result; simp [Except.bind]

def checkArgument (program : Program) (heap : Heap) (args : List Value)
    (check : ArgumentCheck) : Result Unit := do
  let some left := args[check.left]?
    | .error (.typeError "entry guard argument count mismatch")
  let some right := args[check.right]?
    | .error (.typeError "entry guard argument count mismatch")
  match left, right with
  | .ref a, .ref b =>
    if a == b then .error (.typeError "overlapping borrowed arguments")
    else
      if check.leftTraversal == .deep then
        rejectContained program heap b left
      if check.rightTraversal == .deep then
        rejectContained program heap a right
      return ()
  | _, _ => return () -- A missing optional reference has no footprint.

def checkArguments (program : Program) : List ArgumentCheck → Heap → List Value → Result Unit
  | [], _, _ => .ok ()
  | check :: rest, heap, args => do
    checkArgument program heap args check
    checkArguments program rest heap args

theorem checkArguments_iff {program : Program} {plan : List ArgumentCheck} {heap : Heap}
    {args : List Value} : checkArguments program plan heap args = .ok () ↔
      ∀ check ∈ plan, checkArgument program heap args check = .ok () := by
  induction plan with
  | nil => simp [checkArguments]
  | cons check rest ih =>
    simp only [checkArguments, bind, unit_bind_iff, ih, List.mem_cons, forall_eq_or_imp]

theorem checkArgument_iff {program : Program} {heap : Heap} {args : List Value}
    {check : ArgumentCheck} {a b : Nat}
    (left : args[check.left]? = some (.ref a)) (right : args[check.right]? = some (.ref b)) :
    checkArgument program heap args check = .ok () ↔ a ≠ b ∧
      (check.leftTraversal = .deep → containsReference program heap b heap.length [] (.ref a) = .ok false) ∧
      (check.rightTraversal = .deep → containsReference program heap a heap.length [] (.ref b) = .ok false) := by
  cases check with
  | mk leftIndex rightIndex leftTraversal rightTraversal =>
    cases leftTraversal <;> cases rightTraversal <;>
      by_cases same : a = b <;>
      simp [checkArgument, left, right, same, bind, pure, Except.pure,
        unit_bind_iff, rejectContained_iff]

def entrySafe (program : Program) (plan : List ArgumentCheck) (heap : Heap)
    (args : List Value) : Bool := (checkArguments program plan heap args).isOk

theorem entrySafe_iff {program : Program} {plan : List ArgumentCheck} {heap : Heap}
    {args : List Value} : entrySafe program plan heap args = true ↔
      checkArguments program plan heap args = .ok () := by
  unfold entrySafe
  cases checked : checkArguments program plan heap args <;> simp [Except.isOk, Except.toBool]

/-- The exported wrapper throws on overlap before invoking the original
implementation. Its guard is independent of evaluation fuel. -/
def checkedApply (program : Program) (plan : List ArgumentCheck) (fuel : Nat)
    (state : State) (name : String) (args : List Value) : Result (Value × State) := do
  checkArguments program plan state.heap args
  apply program fuel state (.function name) args

def GuardedInvokes (program : Program) (plan : List ArgumentCheck) (before : State)
    (name : String) (args : List Value) (value : Value) (after : State) : Prop :=
  Converges (fun fuel => checkedApply program plan fuel before name args) (.ok (value, after))

theorem guarded_invokes_iff {program : Program} {plan : List ArgumentCheck}
    {before after : State} {name : String} {args : List Value} {value : Value} :
    GuardedInvokes program plan before name args value after ↔
      entrySafe program plan before.heap args = true ∧
      Invokes program before (.function name) args value after := by
  cases guard : checkArguments program plan before.heap args with
  | error error =>
    simp [GuardedInvokes, checkedApply, guard, Converges, entrySafe, Except.isOk,
      Except.toBool, bind, Except.bind]
  | ok result =>
    cases result
    simp only [GuardedInvokes, checkedApply, guard, bind, Except.bind,
      entrySafe, Except.isOk, Except.toBool, true_and]
    rfl

end Ariadne.Ownership
