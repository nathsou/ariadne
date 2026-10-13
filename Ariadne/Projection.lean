import Ariadne.Syntax

namespace Ariadne.Projection

inductive Kind where
  | array
  | map
  deriving Repr, BEq, DecidableEq

structure Path where
  kind : Kind
  container : Expr
  query : Expr
  focus : Expr
  deriving Repr

/-- Container identities are syntactic variable/field paths. Spans do not
change identity; a class may borrow one field while reading an unrelated one. -/
def ownerPath : Expr → Option (List String)
  | .var name _ => some [name]
  | .member object field _ => (ownerPath object).map (· ++ [field])
  | _ => none

def find : Expr → Option Path
  | focus@(.unary "#nonNull" inner _) =>
    match inner with
    | .index .. | .call (.member _ "get" _) [_] _ =>
      (find inner).map fun path => {path with focus}
    | _ => find inner
  | focus@(.index container query _) => some ⟨.array, container, query, focus⟩
  | focus@(.call (.member container "get" _) [query] _) => some ⟨.map, container, query, focus⟩
  | .member object _ _ => find object
  | _ => none

/-- Expression occurrence checks descend into every source argument, including
callback captures. Matching the container stops the walk at that occurrence. -/
def occurrences (path : List String) : Nat → Expr → Nat
  | 0, _ => 1 -- Refuse on exhaustion, rather than overlooking a use.
  | fuel + 1, expression =>
    if ownerPath expression == some path then 1 else
      match expression with
      | .member object _ _ | .unary _ object _ | .spread object _ => occurrences path fuel object
      | .index object query _ | .binary _ object query _ =>
        occurrences path fuel object + occurrences path fuel query
      | .conditional condition yes no _ => occurrences path fuel condition +
          occurrences path fuel yes + occurrences path fuel no
      | .call callee args _ => occurrences path fuel callee +
          (args.map (occurrences path fuel)).foldl Nat.add 0
      | .array values _ | .newClass _ values _ =>
          (values.map (occurrences path fuel)).foldl Nat.add 0
      | .record fields _ =>
          (fields.map (fun field => occurrences path fuel field.2)).foldl Nat.add 0
      | .lambda .. => 1 -- Mutable projections do not accept callback arguments.
      | _ => 0

/-- Keys and update arguments use the pure syntactic fragment. Named calls and
constructors with user bodies cannot mutate the borrowed container indirectly.
Fresh array/record literals still allocate independently of its footprint. -/
def pure : Nat → Expr → Bool
  | 0, _ => false
  | _ + 1, .literal .. | _ + 1, .var .. | _ + 1, .newMap .. | _ + 1, .newSet .. => true
  | fuel + 1, .member expression _ _ | fuel + 1, .unary _ expression _ |
      fuel + 1, .spread expression _ => pure fuel expression
  | fuel + 1, .index left right _ | fuel + 1, .binary _ left right _ =>
      pure fuel left && pure fuel right
  | fuel + 1, .conditional condition yes no _ =>
      pure fuel condition && pure fuel yes && pure fuel no
  | fuel + 1, .array values _ => values.all (pure fuel)
  | fuel + 1, .record fields _ => fields.all (pure fuel ·.2)
  | fuel + 1, .call (.var name _) args _ =>
      ["Number", "BigInt", "#templateString"].contains name && args.all (pure fuel)
  | fuel + 1, .call (.member (.var namespace_ _) method _) args _ =>
      ((namespace_ == "Math" && ["min", "max", "abs", "floor", "trunc", "sqrt"].contains method) ||
        (namespace_ == "Number" && ["isNaN", "isFinite"].contains method)) && args.all (pure fuel)
  | _, _ => false

def exclusive (projection : Path) (otherExpressions : List Expr) : Bool :=
  match ownerPath projection.container with
  | none => false
  | some path =>
    pure 256 projection.query && occurrences path 256 projection.query == 0 &&
      otherExpressions.all (fun expression => pure 256 expression && occurrences path 256 expression == 0)

/-- Substitute only the selected receiver path for native lens elaboration.
The source AST remains unchanged in its certificate and operational semantics. -/
def replaceFocus (span : Span) (name : String) : Nat → Expr → Expr
  | 0, expression => expression
  | fuel + 1, expression =>
    let selectable := match expression with
      | .index .. | .unary "#nonNull" .. | .call (.member _ "get" _) [_] _ => true
      | _ => false
    if selectable && expression.span == span then .var name span else
      match expression with
      | .member object field site => .member (replaceFocus span name fuel object) field site
      | .unary op object site => .unary op (replaceFocus span name fuel object) site
      | .index object query site => .index (replaceFocus span name fuel object) (replaceFocus span name fuel query) site
      | .binary op left right site => .binary op (replaceFocus span name fuel left) (replaceFocus span name fuel right) site
      | .conditional condition yes no site => .conditional (replaceFocus span name fuel condition)
          (replaceFocus span name fuel yes) (replaceFocus span name fuel no) site
      | .call callee args site => .call (replaceFocus span name fuel callee) (args.map (replaceFocus span name fuel)) site
      | other => other

end Ariadne.Projection
