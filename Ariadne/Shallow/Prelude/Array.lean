import Ariadne.Builtins

namespace Ariadne.Shallow.JSArray

def get (xs : List α) (i : Float.Model) : Option α :=
  (Ariadne.indexOf (.number i)).bind (fun n => xs[n]?)

def slice (xs : List α) (start stop : Float.Model) : List α :=
  let bound (x : Float.Model) :=
    let i := x.unpack.toInt (-(Int.ofNat xs.length)) xs.length
    if i < 0 then (max 0 (Int.ofNat xs.length + i)).toNat else min i.toNat xs.length
  (xs.drop (bound start)).take (bound stop - bound start)

def map (f : α → Float.Model → β) (xs : List α) : List β :=
  xs.mapIdx (fun i x => f x (Float.Model.ofNat i))

def filter (f : α → Float.Model → Bool) (xs : List α) : List α :=
  ((xs.zipIdx).filter (fun (x, i) => f x (Float.Model.ofNat i))).map Prod.fst

def reduce (f : β → α → Float.Model → β) (initial : β) (xs : List α) : β :=
  xs.zipIdx.foldl (fun acc (x, i) => f acc x (Float.Model.ofNat i)) initial

def some (f : α → Float.Model → Bool) (xs : List α) : Bool :=
  xs.zipIdx.any (fun (x, i) => f x (Float.Model.ofNat i))
def every (f : α → Float.Model → Bool) (xs : List α) : Bool :=
  xs.zipIdx.all (fun (x, i) => f x (Float.Model.ofNat i))
def find (f : α → Float.Model → Bool) (xs : List α) : Option α :=
  (xs.zipIdx.find? (fun (x, i) => f x (Float.Model.ofNat i))).map Prod.fst
def findIndex (f : α → Float.Model → Bool) (xs : List α) : Float.Model :=
  Float.Model.ofInt ((xs.zipIdx.findIdx? (fun (x, i) => f x (Float.Model.ofNat i))).map Int.ofNat |>.getD (-1))

@[simp] theorem map_unindexed (f : α → β) (xs : List α) : map (fun x _ => f x) xs = xs.map f := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa only [map, List.mapIdx_cons, List.map_cons] using congrArg (f x :: ·) ih

@[simp] theorem reduce_unindexed (f : β → α → β) (initial : β) (xs : List α) :
    reduce (fun acc x _ => f acc x) initial xs = xs.foldl f initial := by
  have h := congrArg (List.foldl f initial) (List.zipIdx_map_fst 0 xs)
  simpa only [reduce, List.foldl_map] using h

@[simp] theorem filter_unindexed (f : α → Bool) (xs : List α) :
    filter (fun x _ => f x) xs = xs.filter f := by
  have h := congrArg (List.filter f) (List.zipIdx_map_fst 0 xs)
  simpa only [filter, List.filter_map, Function.comp_def] using h

end Ariadne.Shallow.JSArray
