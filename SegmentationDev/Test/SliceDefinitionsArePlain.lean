import Lean
import Segmentation

-- "No `partial def` anywhere in the proved path: a `partial def` has no equation lemmas, so the
-- proof cannot unfold it."
-- A `partial` definition is stored as an opaque constant and a compiler substitute is recorded as
-- an attribute, so neither shows up as an axiom; the keyword scan does not look for `partial`.
open Lean in
theorem «slice_scanner_definitions_are_plain_with_no_compiled_substitute» : True := by
  run_tac do
    let env ← getEnv
    for name in [``Segmentation.sliceGraphemes, ``Segmentation.sliceBoundaries,
        ``Segmentation.charProps, ``Segmentation.asciiProps] do
      match env.find? name with
      | some (.defnInfo _) => pure ()
      | some _ => throwError m!"{name} is not a plain definition (a partial definition is opaque)"
      | none => throwError m!"{name} is missing"
      if (Compiler.getImplementedBy? env name).isSome then
        throwError m!"{name} has a compiled substitute the proof does not cover"
      if isExtern env name then
        throwError m!"{name} is bound to foreign code the proof does not cover"
  trivial
