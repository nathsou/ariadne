import Ariadne.Shallow.Prelude.NumericCollections

namespace Ariadne.Shallow.Core

/-- Collection keys use scalar value equality. Numeric keys select the separate
SameValueZero representation, including insertion-time zero normalization. -/
inductive Key where
  | int | number | string | bool
  deriving Repr, DecidableEq, BEq, Inhabited

abbrev Key.denote : Key → Type
  | .int => Int
  | .number => Float.Model
  | .string => JSString
  | .bool => Bool

abbrev Key.Map : Key → Type → Type
  | .int, υ => JSMap Int υ
  | .number, υ => NumberMap υ
  | .string, υ => JSMap JSString υ
  | .bool, υ => JSMap Bool υ

abbrev Key.Set : Key → Type
  | .int => JSSet Int
  | .number => NumberSet
  | .string => JSSet JSString
  | .bool => JSSet Bool

def Key.mapEmpty (k : Key) {υ : Type} : k.Map υ :=
  match k with
  | .number => NumberMap.empty
  | .int | .string | .bool => JSMap.empty

def Key.setEmpty (k : Key) : k.Set :=
  match k with
  | .number => NumberSet.empty
  | .int | .string | .bool => JSSet.empty

end Ariadne.Shallow.Core
