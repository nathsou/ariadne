import Lean

namespace Ariadne

/-- Half-open UTF-8 byte offsets into the original source file. -/
structure Span where
  start : Nat := 0
  stop : Nat := 0
  deriving Repr, BEq, Inhabited

structure Source where
  path : String
  text : String
  deriving Repr, Inhabited

structure Label where
  span : Span
  message : String
  deriving Repr, Inhabited

/-- Diagnostics are data; terminal and editor renderers share the same payload. -/
structure Diagnostic where
  code : String
  message : String
  span : Span := {}
  notes : List String := []
  labels : List Label := []
  help : Option String := none
  deriving Repr, Inhabited

abbrev Checked := Except Diagnostic

def Source.position (source : Source) (offset : Nat) : Nat × Nat := Id.run do
  let mut line := 1
  let mut column := 1
  let mut bytes := 0
  for c in source.text.toList do
    if bytes >= offset then break
    bytes := bytes + c.utf8Size
    if c == '\n' then
      line := line + 1
      column := 1
    else
      column := column + 1
  return (line, column)

def Diagnostic.render (d : Diagnostic) (source : Source) : String := Id.run do
  let (line, column) := source.position d.span.start
  let sourceLine := (source.text.splitOn "\n")[line - 1]?.getD ""
  let (_, endColumn) := source.position d.span.stop
  let width := max 1 (min (sourceLine.length + 1 - column) (endColumn - column))
  let padding := String.ofList (List.replicate (column - 1) ' ')
  let marker := String.ofList (List.replicate width '^')
  let mut out := s!"error[{d.code}]: {d.message}\n  --> {source.path}:{line}:{column}\n   |\n{line} | {sourceLine}\n   | {padding}{marker}\n"
  for label in d.labels do
    let (l, c) := source.position label.span.start
    out := out ++ s!"   = related: {source.path}:{l}:{c}: {label.message}\n"
  for note in d.notes do
    out := out ++ s!"   = note: {note}\n"
  if let some help := d.help then
    out := out ++ s!"   = help: {help}\n"
  return out

def Diagnostic.toJson (d : Diagnostic) (source : Source) : Lean.Json :=
  let (line, column) := source.position d.span.start
  Lean.Json.mkObj [
    ("schemaVersion", Lean.toJson (1 : Nat)),
    ("severity", Lean.toJson "error"), ("code", Lean.toJson d.code),
    ("message", Lean.toJson d.message), ("file", Lean.toJson source.path),
    ("startByte", Lean.toJson d.span.start), ("endByte", Lean.toJson d.span.stop),
    ("line", Lean.toJson line), ("column", Lean.toJson column),
    ("notes", Lean.toJson d.notes), ("help", Lean.toJson d.help),
    ("related", Lean.Json.arr (d.labels.toArray.map fun l => Lean.Json.mkObj [
      ("startByte", Lean.toJson l.span.start), ("endByte", Lean.toJson l.span.stop),
      ("message", Lean.toJson l.message)]))]

end Ariadne
