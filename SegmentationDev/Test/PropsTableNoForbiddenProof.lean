import Lean
import SegmentationDev.Gate.Axioms
import Segmentation

-- "The proof uses no axiom beyond `propext`, `Classical.choice` and `Quot.sound`, and no
-- `sorry`, `native_decide`, `implemented_by`, `extern` or `partial` (CI's forbidden-words scan
-- rejects most of these)."
-- A proof by `sorry` leaves `sorryAx` and one by compiler evaluation leaves `Lean.ofReduceBool`
-- among the theorem's axioms. A `partial` definition is stored as an opaque constant, and a
-- compiler substitute is recorded as an attribute, so neither shows up as an axiom: the
-- definitions the theorem is about are checked for both directly. The keyword scan does not
-- look for `partial` at all, so this is the only automated check of it.
open Lean in
theorem «propsLookup_eq_props rests on no sorry, compiler-evaluated proof, compiler substitute or partial definition» :
    True := by
  run_tac do
    let used ← collectAxioms ``Segmentation.Tables.propsLookup_eq_props
    let bad := SegmentationDev.Gate.disallowedAxioms used
    unless bad.isEmpty do
      throwError m!"propsLookup_eq_props uses disallowed axioms {bad}"
    let env ← getEnv
    for name in [``Segmentation.Tables.propsLookup, ``Segmentation.Tables.propsRanges,
        ``Segmentation.Tables.Range.mergeWith] do
      match env.find? name with
      | some (.defnInfo _) => pure ()
      | some _ => throwError m!"{name} is not a plain definition (a partial definition is opaque)"
      | none => throwError m!"{name} is missing"
      if (Compiler.getImplementedBy? env name).isSome then
        throwError m!"{name} has a compiled substitute the proof does not cover"
      if isExtern env name then
        throwError m!"{name} is bound to foreign code the proof does not cover"
  trivial
