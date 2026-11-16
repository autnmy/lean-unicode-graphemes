import Lean
import Segmentation

-- "Make `scanClusters` call `breaksBeforeFast`, and update `scanClusters_agree` to rewrite with
-- the equality, so `sliceGraphemes_agree`, `graphemes_eq_graphemesFast` and
-- `boundaries_eq_boundariesFast` still prove."
open Lean in
/-- The three agreement theorems are still proved theorems, and the scan proof they rest on
rewrites with the equality between the fast break decision and the reference one. -/
theorem slice_agreement_theorems_still_prove_through_breaks_before_fast_equality : True := by
  run_tac do
    let env ← getEnv
    for name in [``Segmentation.sliceGraphemes_agree, ``Segmentation.graphemes_eq_graphemesFast,
        ``Segmentation.boundaries_eq_boundariesFast, ``Segmentation.scanClusters_agree] do
      match env.find? name with
      | some (.thmInfo _) => pure ()
      | some _ => throwError m!"{name} is not a theorem"
      | none => throwError m!"{name} is missing"
    -- Follow the proof term and the auxiliary declarations under `scanClusters_agree`, because
    -- structural recursion can place the body in a generated helper.
    let mut seen : NameSet := {}
    let mut todo : Array Name := #[``Segmentation.scanClusters_agree]
    let mut i := 0
    while i < todo.size do
      let n := todo[i]!
      i := i + 1
      if seen.contains n then continue
      seen := seen.insert n
      if (``Segmentation.scanClusters_agree).isPrefixOf n then
        match env.find? n with
        | some info =>
          match info.value? (allowOpaque := true) with
          | some v => for c in v.getUsedConstants do todo := todo.push c
          | none => pure ()
        | none => pure ()
    unless seen.contains ``Segmentation.breaksBeforeFast_eq_breaksBefore do
      throwError "scanClusters_agree does not rewrite with breaksBeforeFast_eq_breaksBefore"
  trivial
