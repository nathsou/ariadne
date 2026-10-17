import Ariadne.Front.Print

/-! Compatibility import for the frontend API.
Checking and code construction live in `Front.Elaborate`; declaration assembly
and translation entry points live in `Front.Print`; emission trees in `Front.Emit`.
All generated models are still checked against the shared denotation. -/
