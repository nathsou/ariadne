/-! Small, untrusted emission trees. Declarations and references survive composition;
the final pass prints them, without sentinel strings or parsing generated Lean. -/
namespace Ariadne.Front

inductive Code where
  | text (value : String)
  | append (left right : Code)
  | binding (name type : String) (value body : Code) (indent : String)
  | hoisted (id : Nat) (params type args : String) (body : Code)
  deriving Inhabited

instance : Coe String Code := ⟨Code.text⟩
instance : Append Code := ⟨Code.append⟩
instance : HAppend String Code Code := ⟨fun a b => .append (.text a) b⟩
instance : HAppend Code String Code := ⟨fun a b => .append a (.text b)⟩

class ToCode (α : Type) where
  toCode : α → Code
export ToCode (toCode)
instance : ToCode Code := ⟨id⟩
instance [ToString α] : ToCode α := ⟨fun x => .text (toString x)⟩

syntax:max "c!" interpolatedStr(term) : term
macro_rules
  | `(c! $s) => do s.expandInterpolatedStr (← `(Code)) (← `(toCode))

namespace Code

/-- Rendering is the only place code becomes text. Eliminate only the administrative
binding `let x := value; x`; useful sharing and source bindings otherwise remain. -/
def render (loopName : Nat → String) : Code → String
  | .text s => s
  | .append a b => a.render loopName ++ b.render loopName
  | .binding n ty v b i =>
    let body := b.render loopName
    if body == n then v.render loopName
    else
      let value := v.render loopName
      let space := if value.startsWith "\n" then "" else " "
      s!"let {n}{if ty.isEmpty then "" else s!" : {ty}"} :={space}{value}\n{i}{body}"
  | .hoisted id _ _ args _ =>
    if args.isEmpty then loopName id else s!"({loopName id} {args})"

def preview (c : Code) : String := c.render (fun n => s!"loop{n}'")

def intercalate (separator : String) : List Code → Code
  | [] => .text ""
  | [x] => x
  | x :: xs => x ++ separator ++ intercalate separator xs

/-- References in source traversal order; repeated branches share the same declaration. -/
def loopIds : Code → List Nat
  | .text _ => []
  | .append a b => a.loopIds ++ b.loopIds
  | .binding _ _ v b _ => v.loopIds ++ b.loopIds
  | .hoisted id _ _ _ body => id :: body.loopIds

/-- Dependencies precede their users. The declaration tree, not rendered text, determines order. -/
def declarations (loopName : Nat → String) : Code → List (Nat × String)
  | .text _ => []
  | .append a b => a.declarations loopName ++ b.declarations loopName
  | .binding _ _ v b _ => v.declarations loopName ++ b.declarations loopName
  | .hoisted id params ty _ body => body.declarations loopName ++
      [(id, s!"def {loopName id}{params} : {ty} :=\n  {body.render loopName}")]

def emit (functionName : String) (code : Code) : String × List String := Id.run do
  let ids := code.loopIds.eraseDups
  let name (n : Nat) := if ids.length == 1 then s!"{functionName}.loop"
    else s!"{functionName}.loop{ids.idxOf n + 1}"
  let mut seen : List Nat := []
  let mut defs : List String := []
  for (n, declaration) in code.declarations name do
    if !seen.contains n then
      seen := n :: seen
      defs := defs ++ [declaration]
  return (code.render name, defs)

end Code
end Ariadne.Front
