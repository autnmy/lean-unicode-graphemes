import Lean
import Segmentation

-- "`scanClusters` is a tail loop that pushes cluster bounds into an `Array`, and
-- `sliceGraphemes_agree` and both `@[csimp]` lemmas still prove."
-- "No `sorry`, no `implemented_by` or `@[extern]` that the proof does not cover, no `partial def`
-- in the proved path."
-- `sorry` shows up as the `sorryAx` axiom, so only the three standard axioms are allowed. The scan
-- lemma must speak about the Array the new loop accumulates into, so the old List statement fails.
open Lean in
/-- The scan agreement, sliceGraphemes_agree and both csimp lemmas are theorems using only the standard axioms, and the scan agreement is stated over the Array accumulator. -/
theorem slice_agreement_and_csimp_lemmas_prove_over_array_scan : True := by
  run_tac do
    let env ← getEnv
    let allowed := [``propext, ``Classical.choice, ``Quot.sound]
    for name in [``Segmentation.scanClusters_agree, ``Segmentation.sliceGraphemes_agree,
        ``Segmentation.graphemes_eq_graphemesFast, ``Segmentation.boundaries_eq_boundariesFast] do
      match env.find? name with
      | some (.thmInfo _) => pure ()
      | some _ => throwError m!"{name} is not a theorem"
      | none => throwError m!"{name} is missing"
      for ax in ← collectAxioms name do
        unless allowed.contains ax do
          throwError m!"{name} depends on the axiom {ax}"
    let some agree := env.find? ``Segmentation.scanClusters_agree
      | throwError "scanClusters_agree is missing"
    unless agree.type.getUsedConstants.any (fun c => (`Array).isPrefixOf c) do
      throwError "scanClusters_agree is not stated over the Array the scan accumulates into"
  trivial
