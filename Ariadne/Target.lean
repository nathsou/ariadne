import Ariadne.Semantics

namespace Ariadne.Target

/-- Target fragments are Lean functions, not syntax interpreted at runtime. The
first backend keeps explicit cells; replacing them by tuples is a later pass. -/
abbrev Expression := Nat → State → Result (Value × State)
abbrev Command := Nat → State → Result Completion

def literal (value : Literal) : Expression
  | 0, _ => .error .timeout
  | _ + 1, s => .ok (Value.ofLiteral value, s)

def read (name : String) : Expression
  | 0, _ => .error .timeout
  | _ + 1, s => do
    if s.env.any (fun p => p.1 == name) then return (← s.lookup name, s)
    if name == "NaN" then return (.number Float.Model.nan, s)
    if name == "Infinity" then return (.number Float.Model.inf, s)
    return (.function name, s)

def unary (op : String) (arg : Expression) : Expression
  | 0, _ => .error .timeout
  | n + 1, s => do
    let (v, s) ← arg n s
    return (← Ariadne.unary op v, s)

def binary (op : String) (left right : Expression) : Expression
  | 0, _ => .error .timeout
  | n + 1, s => do
    let (a, s) ← left n s
    if op == "&&" && !a.truthy then return (a, s)
    if op == "||" && a.truthy then return (a, s)
    if op == "??" && a != .undefined && a != .null then return (a, s)
    let (b, s) ← right n s
    if ["&&", "||", "??"].contains op then return (b, s)
    return (← Ariadne.binary op a b, s)

def conditional (guard yes no : Expression) : Expression
  | 0, _ => .error .timeout
  | n + 1, s => do
    let (v, s) ← guard n s
    (if v.truthy then yes else no) n s

def member (object : Expression) (field : String) : Expression
  | 0, _ => .error .timeout
  | n + 1, s => do
    let (v, s) ← object n s
    return (← readMember s v field, s)

def index (object offset : Expression) : Expression
  | 0, _ => .error .timeout
  | n + 1, s => do
    let (v, s) ← object n s
    let (i, s) ← offset n s
    return (← readIndex s v i, s)

/-- Sequence consumes the same depth budget as the source block evaluator. -/
def sequence (first rest : Command) : Command
  | 0, _ => .error .timeout
  | n + 1, s => do
    let out ← first n s
    if out.control != .normal then return out
    rest n out.state

def empty : Command
  | 0, _ => .error .timeout
  | _ + 1, s => .ok { state := s }

def scope (body : Command) : Command
  | 0, _ => .error .timeout
  | n + 1, s => do
    let out ← body n s
    return { out with state := { out.state with env := s.env } }

def declare (name : String) (value : Expression) : Command
  | 0, _ => .error .timeout
  | n + 1, s => do
    let (v, s) ← value n s
    return { state := s.declare name v }

def assign (name : String) (value : Expression) : Command
  | 0, _ | 1, _ => .error .timeout
  | n + 2, s => do
    let (v, s) ← value n s
    return { state := ← s.assign name v }

def discard (value : Expression) : Command
  | 0, _ => .error .timeout
  | n + 1, s => do
    let (_, s) ← value n s
    return { state := s }

def branch (guard : Expression) (yes no : Command) : Command
  | 0, _ => .error .timeout
  | n + 1, s => do
    let (v, s) ← guard n s
    (if v.truthy then yes else no) n s

/-- Break exits normally; return propagates; continue still runs the update. -/
def loop (guard : Expression) (body : Command) (update : Option Command) : Command
  | 0, _ => .error .timeout
  | n + 1, s => do
    let (v, s) ← guard n s
    if !v.truthy then return { state := s }
    let out ← body n s
    if out.control == .returned then return out
    if out.control == .broke then return { state := out.state }
    let s ← match update with
      | none => pure out.state
      | some step => (step n out.state).map Completion.state
    loop guard body update n s

def while_ (guard : Expression) (body : Command) : Command
  | 0, _ => .error .timeout
  | n + 1, s => loop guard body none n s

def for_ (init : Command) (guard : Expression) (update body : Command) : Command
  | 0, _ => .error .timeout
  | n + 1, s => do
    let initial ← init n s
    let out ← loop guard body (some update) n initial.state
    return { out with state := { out.state with env := s.env } }

def return_ (value : Expression) : Command
  | 0, _ => .error .timeout
  | n + 1, s => do
    let (v, s) ← value n s
    return { control := .returned, value := v, state := s }

def break_ : Command
  | 0, _ => .error .timeout
  | _ + 1, s => .ok { control := .broke, state := s }

def continue_ : Command
  | 0, _ => .error .timeout
  | _ + 1, s => .ok { control := .continued, state := s }

/-- Includes the source's call dispatch and frame budgets. -/
def function (params : List Param) (body : Command)
    (fuel : Nat) (s : State) (args : List Value) : Result (Value × State) := do
  match fuel with
  | 0 | 1 => throw .timeout
  | n + 2 =>
    let frame := (params.zip args).foldl (fun s (p, v) => s.declare p.name v) { s with env := [] }
    let out ← body n frame
    if out.control == .broke || out.control == .continued then
      throw (.invariant "loop control escaped a function")
    return (out.value, { out.state with env := s.env })

end Ariadne.Target
