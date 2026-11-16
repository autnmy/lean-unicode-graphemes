import Lean
import Segmentation

-- "No `sorry`, no `implemented_by` or `@[extern]` that the proof does not cover, no `partial def`
-- in the proved path."
-- A partial definition is stored as an opaque constant, and a compiled substitute is an attribute,
-- so neither shows up as an axiom; this reads each new helper's kind and attributes directly.
open Lean in
/-- The ASCII decision, the ASCII state and the array-returning scan are plain definitions with no
compiled substitute and no foreign binding. -/
theorem ascii_path_helpers_are_plain_definitions_with_no_compiled_substitute : True := by
  run_tac do
    let env ← getEnv
    for name in [``Segmentation.asciiBreaksBefore, ``Segmentation.asciiState,
        ``Segmentation.scanClusters, ``Segmentation.clusterBounds] do
      match env.find? name with
      | some (.defnInfo _) => pure ()
      | some _ => throwError m!"{name} is not a plain definition"
      | none => throwError m!"{name} is missing"
      if (Compiler.getImplementedBy? env name).isSome then
        throwError m!"{name} has a compiled substitute the proof does not cover"
      if isExtern env name then
        throwError m!"{name} is bound to foreign code the proof does not cover"
  trivial
