import Ariadne.Convergence
import Ariadne.Shallow.Denote

namespace Ariadne.Shallow.Adequacy
open Core

inductive Scalar : Core.Ty → Type where
  | unit : Scalar .unit
  | bool : Scalar .bool
  | int : Scalar .int
  | int53 : Scalar .int53
  | number : Scalar .number
  | string : Scalar .string

def Scalar.encode {interp : Named.Interp} : Scalar t → t.denote interp → Value
  | .unit, _ => .undefined
  | .bool, b => .boolean b
  | .int, n => .bigint n
  | .int53, n => .number (Float.Model.ofInt n)
  | .number, n => .number n
  | .string, s => .string s

inductive UnaryRule : {a b : Core.Ty} → Scalar a → Scalar b → String → Unary a b → Prop where
  | not : UnaryRule .bool .bool "!" .not
  | intNeg : UnaryRule .int .int "-" .intNeg
  | numNeg : UnaryRule .number .number "-" .numNeg

theorem UnaryRule.correct {sa : Scalar a} {sb : Scalar b} {source : String} {op : Unary a b}
    (rule : UnaryRule sa sb source op) (interp : Named.Interp) (input : a.denote interp) :
    Ariadne.unary source (sa.encode input) = .ok (sb.encode (Denote.unary op input)) := by
  cases rule <;> rfl

inductive BinaryRule : {a b c : Core.Ty} → Scalar a → Scalar b → Scalar c → String → Binary a b c → Prop where
  | intAdd : BinaryRule .int .int .int "+" .intAdd
  | intSub : BinaryRule .int .int .int "-" .intSub
  | intMul : BinaryRule .int .int .int "*" .intMul
  | intEq : BinaryRule .int .int .bool "===" .intEq
  | intLt : BinaryRule .int .int .bool "<" .intLt
  | intLe : BinaryRule .int .int .bool "<=" .intLe
  | numAdd : BinaryRule .number .number .number "+" .numAdd
  | numSub : BinaryRule .number .number .number "-" .numSub
  | numMul : BinaryRule .number .number .number "*" .numMul
  | numDiv : BinaryRule .number .number .number "/" .numDiv
  | numMod : BinaryRule .number .number .number "%" .numMod
  | numEq : BinaryRule .number .number .bool "===" .numEq
  | numLt : BinaryRule .number .number .bool "<" .numLt
  | numLe : BinaryRule .number .number .bool "<=" .numLe
  | strAppend : BinaryRule .string .string .string "+" .strAppend
  | strEq : BinaryRule .string .string .bool "===" .strEq
  | strLt : BinaryRule .string .string .bool "<" .strLt
  | strLe : BinaryRule .string .string .bool "<=" .strLe
  | boolEq : BinaryRule .bool .bool .bool "===" .boolEq

theorem BinaryRule.strict {sa : Scalar a} {sb : Scalar b} {sc : Scalar c}
    {source : String} {op : Binary a b c} (rule : BinaryRule sa sb sc source op) :
    source ≠ "&&" ∧ source ≠ "||" ∧ source ≠ "??" := by cases rule <;> decide

theorem BinaryRule.correct {sa : Scalar a} {sb : Scalar b} {sc : Scalar c}
    {source : String} {op : Binary a b c} (rule : BinaryRule sa sb sc source op)
    (interp : Named.Interp) (left : a.denote interp) (right : b.denote interp) :
    Ariadne.binary source (sa.encode left) (sb.encode right) =
      .ok (sc.encode (Denote.binary op left right)) := by
  cases rule <;> rfl

inductive SwappedBinaryRule : {a b c : Core.Ty} → Scalar a → Scalar b → Scalar c → String → Binary b a c → Prop where
  | intGt : SwappedBinaryRule .int .int .bool ">" .intLt
  | intGe : SwappedBinaryRule .int .int .bool ">=" .intLe
  | numGt : SwappedBinaryRule .number .number .bool ">" .numLt
  | numGe : SwappedBinaryRule .number .number .bool ">=" .numLe
  | strGt : SwappedBinaryRule .string .string .bool ">" .strLt
  | strGe : SwappedBinaryRule .string .string .bool ">=" .strLe
theorem SwappedBinaryRule.correct {sa : Scalar a} {sb : Scalar b} {sc : Scalar c}
    {source : String} {op : Binary b a c} (rule : SwappedBinaryRule sa sb sc source op)
    (interp : Named.Interp) (left : a.denote interp) (right : b.denote interp) :
    Ariadne.binary source (sa.encode left) (sb.encode right) =
      .ok (sc.encode (Denote.binary op right left)) := by
  cases rule <;> try rfl
  all_goals
    simp only [Ariadne.binary, Scalar.encode, Denote.binary]
    rw [Std.OrientedOrd.eq_swap (a := left) (b := right)]
    cases compare right left <;> rfl

theorem SwappedBinaryRule.strict {sa : Scalar a} {sb : Scalar b} {sc : Scalar c}
    {source : String} {op : Binary b a c} (rule : SwappedBinaryRule sa sb sc source op) :
    source ≠ "&&" ∧ source ≠ "||" ∧ source ≠ "??" := by cases rule <;> decide

structure Names (Γ : List Core.Ty) where
  get : ∀ {t}, Var Γ t → String
  /-- Rebinding a source name hides its previous Core versions. -/
  visible : ∀ {t}, Var Γ t → Bool := fun _ => true

def Names.fromList (names : List String) : Names Γ := { get := fun v => get names v }
where
  get {types : List Core.Ty} {t : Core.Ty} : List String → Var types t → String
    | [], _ => ""
    | name :: _, .here => name
    | _ :: names, .there v => get names v

def Environment {interp : Named.Interp} (names : Names Γ) (state : State) (env : Core.Env Γ interp) : Prop :=
  ∀ {t} (v : Var Γ t) (scalar : Scalar t), names.visible v = true →
    state.lookup (names.get v) = .ok (scalar.encode (v.get env))

/-- A syntax-directed correspondence witness for the pure scalar expression
fragment. This relates the original source AST to an actual typed Core term;
there is no alternative evaluator. Extending coverage requires new proved rules. -/
inductive ScalarExpr {Γ : List Core.Ty} (names : Names Γ) : {t : Core.Ty} → Scalar t → Expr → Term Γ t → Prop where
  | unit (span) : ScalarExpr names .unit (.literal .undefined span) .unit
  | bool (b span) : ScalarExpr names .bool (.literal (.boolean b) span) (.bool b)
  | int (n span) : ScalarExpr names .int (.literal (.bigint n) span) (.int n)
  | number (m e span) : ScalarExpr names .number (.literal (.number m e) span) (.number m e)
  | string (s span) : ScalarExpr names .string (.literal (.string s) span) (.string s)
  | var (scalar : Scalar t) (v : Var Γ t) (span) (visible : names.visible v = true) :
      ScalarExpr names scalar (.var (names.get v) span) (.var v)
  | unary {a b : Core.Ty} {sa : Scalar a} {sb : Scalar b} {source : String}
      {op : Unary a b} {arg : Expr} {term : Term Γ a} (rule : UnaryRule sa sb source op) (input : ScalarExpr names sa arg term) (span) :
      ScalarExpr names sb (.unary source arg span) (.unary op term)
  | notIte {arg : Expr} {term : Term Γ .bool} (input : ScalarExpr names .bool arg term) (span) :
      ScalarExpr names .bool (.unary "!" arg span) (.ite term (.bool false) (.bool true))
  | boolIte {arg : Expr} {term : Term Γ .bool} (input : ScalarExpr names .bool arg term) :
      ScalarExpr names .bool arg (.ite term (.bool true) (.bool false))
  | binary {ta tb tc : Core.Ty} {sa : Scalar ta} {sb : Scalar tb} {sc : Scalar tc}
      {source : String} {op : Binary ta tb tc} {lhs rhs : Expr} {a : Term Γ ta} {b : Term Γ tb} (rule : BinaryRule sa sb sc source op)
      (left : ScalarExpr names sa lhs a) (right : ScalarExpr names sb rhs b) (span) :
      ScalarExpr names sc (.binary source lhs rhs span) (.binary op a b)
  | binarySwap {ta tb tc : Core.Ty} {sa : Scalar ta} {sb : Scalar tb} {sc : Scalar tc}
      {source : String} {op : Binary tb ta tc} {lhs rhs : Expr} {a : Term Γ ta} {b : Term Γ tb}
      (rule : SwappedBinaryRule sa sb sc source op)
      (left : ScalarExpr names sa lhs a) (right : ScalarExpr names sb rhs b) (span) :
      ScalarExpr names sc (.binary source lhs rhs span) (.binary op b a)
  | conditional {t : Core.Ty} {scalar : Scalar t} {condition yesExpr noExpr : Expr}
      {c : Term Γ .bool} {a b : Term Γ t} (test : ScalarExpr names .bool condition c)
      (yes : ScalarExpr names scalar yesExpr a) (no : ScalarExpr names scalar noExpr b) (span) :
      ScalarExpr names scalar (.conditional condition yesExpr noExpr span) (.ite c a b)
  | and {lhs rhs : Expr} {a b : Term Γ .bool} (left : ScalarExpr names .bool lhs a) (right : ScalarExpr names .bool rhs b) (span) :
      ScalarExpr names .bool (.binary "&&" lhs rhs span) (.ite a b (.bool false))
  | or {lhs rhs : Expr} {a b : Term Γ .bool} (left : ScalarExpr names .bool lhs a) (right : ScalarExpr names .bool rhs b) (span) :
      ScalarExpr names .bool (.binary "||" lhs rhs span) (.ite a (.bool true) b)

/-- Fundamental lemma for this expression fragment, for every interpretation
and every matching operational environment. The final state is unchanged. -/
theorem ScalarExpr.sound {names : Names Γ} {scalar : Scalar t} {source : Expr} {term : Term Γ t}
    (translation : ScalarExpr names scalar source term) (program : Program) (interp : Named.Interp)
    (state : State) (env : Core.Env Γ interp) (related : Environment names state env) :
    Evaluates program state source (scalar.encode (Denote.term term env)) state := by
  induction translation with
  | unit span => exact Evaluates.literal program state .undefined span
  | bool b span => exact Evaluates.literal program state (.boolean b) span
  | int n span => exact Evaluates.literal program state (.bigint n) span
  | number m e span => exact Evaluates.literal program state (.number m e) span
  | string s span => exact Evaluates.literal program state (.string s) span
  | var scalar v span visible =>
    exact Evaluates.variable program state _ span _ (State.lookup_present (related v scalar visible)) (related v scalar visible)
  | unary rule input span ih =>
    exact ih.unary _ span (rule.correct interp _)
  | @notIte arg term input span ih =>
    have h := ih.unary "!" span (UnaryRule.not.correct interp _)
    cases value : Denote.term term env <;> simpa [Denote.term, Denote.unary, Scalar.encode, value] using h
  | @boolIte arg term input ih =>
    cases value : Denote.term term env <;> simpa [Denote.term, Scalar.encode, value] using ih
  | binary rule left right span ihl ihr =>
    exact ihl.binary ihr _ span rule.strict (rule.correct interp _ _)
  | binarySwap rule left right span ihl ihr =>
    exact ihl.binary ihr _ span rule.strict (rule.correct interp _ _)
  | @conditional _ repr _ yesExpr noExpr c a b test yes no span ihc ihy ihn =>
    cases value : Denote.term c env
    · have branch : Evaluates program state
          (if (Scalar.bool.encode (Denote.term c env)).truthy then yesExpr else noExpr)
          (repr.encode (Denote.term b env)) state := by simpa [Scalar.encode, Value.truthy, value] using ihn
      simpa [Denote.term, value] using Evaluates.conditional ihc branch span
    · have branch : Evaluates program state
          (if (Scalar.bool.encode (Denote.term c env)).truthy then yesExpr else noExpr)
          (repr.encode (Denote.term a env)) state := by simpa [Scalar.encode, Value.truthy, value] using ihy
      simpa [Denote.term, value] using Evaluates.conditional ihc branch span
  | @and _ _ a b left right span ihl ihr =>
    cases value : Denote.term a env
    · simpa [Denote.term, Denote.binary, Scalar.encode, value] using ihl.and_false (right := _) (by simp [Scalar.encode, Value.truthy, value]) span
    · simpa [Denote.term, Denote.binary, Scalar.encode, value] using ihl.and_true ihr (by simp [Scalar.encode, Value.truthy, value]) span
  | @or _ _ a b left right span ihl ihr =>
    cases value : Denote.term a env
    · simpa [Denote.term, Denote.binary, Scalar.encode, value] using ihl.or_false ihr (by simp [Scalar.encode, Value.truthy, value]) span
    · simpa [Denote.term, Denote.binary, Scalar.encode, value] using ihl.or_true (right := _) (by simp [Scalar.encode, Value.truthy, value]) span

end Ariadne.Shallow.Adequacy
