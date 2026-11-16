import Lean
import Segmentation

-- "`scanClusters` uses `breaksBeforeFast`, and `sliceGraphemes_agree`,
-- `graphemes_eq_graphemesFast` and `boundaries_eq_boundariesFast` still prove."
open Lean in
/-- The definitions reachable from scanClusters reach breaksBeforeFast and never the reference
breaksBefore. The agreement proofs hold whichever decision the scanner calls, so only the
definitions themselves can show which one runs. -/
theorem scan_clusters_decides_with_breaks_before_fast : True := by
  run_tac do
    let env ← getEnv
    let mut seen : NameSet := {}
    let mut todo : Array Name := #[``Segmentation.scanClusters]
    let mut i := 0
    while i < todo.size do
      let n := todo[i]!
      i := i + 1
      if n == ``Segmentation.breaksBefore then
        throwError m!"Segmentation.scanClusters reaches the reference Segmentation.breaksBefore"
      if seen.contains n then continue
      seen := seen.insert n
      if (`Segmentation).isPrefixOf n then
        match env.find? n with
        | some (.defnInfo info) =>
          for c in info.value.getUsedConstants do
            todo := todo.push c
        | _ => pure ()
    unless seen.contains ``Segmentation.breaksBeforeFast do
      throwError m!"Segmentation.scanClusters does not reach Segmentation.breaksBeforeFast"
  trivial
