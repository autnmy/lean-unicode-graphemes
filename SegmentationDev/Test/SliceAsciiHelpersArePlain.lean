import Lean
import Segmentation

-- "`Segmentation/Statements.lean` is byte-for-byte unchanged, and every new helper is in the
-- plain-definition check and the axiom gate."
-- A `partial` definition is stored as an opaque constant and a compiler substitute is an
-- attribute, so neither shows as an axiom; this checks the constant kind and the attributes.
open Lean in
/-- The ASCII decision and ASCII state are plain definitions with no compiled substitute and no foreign binding. -/
theorem slice_ascii_helpers_are_plain_with_no_compiled_substitute : True := by
  run_tac do
    let env ← getEnv
    for name in [``Segmentation.asciiBreaksBefore, ``Segmentation.asciiState] do
      match env.find? name with
      | some (.defnInfo _) => pure ()
      | some _ => throwError m!"{name} is not a plain definition (a partial definition is opaque)"
      | none => throwError m!"{name} is missing"
      if (Compiler.getImplementedBy? env name).isSome then
        throwError m!"{name} has a compiled substitute the proof does not cover"
      if isExtern env name then
        throwError m!"{name} is bound to foreign code the proof does not cover"
  trivial
