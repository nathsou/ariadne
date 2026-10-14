import Lean

/-!
# `readable`: the simp set of the readable names

A translated file gives the source's named types readable names (accessors, literal constants, variant
constructors), all tagged `readable`. `simp [readable]` unfolds them into the projections, numerals and
injections the readable definitions use, so statements written with them meet the definitions.
-/

register_simp_attr readable
