import Lean
import Bench.Libraries

-- "Add a fast clusters function that calls `Segmentation.sliceGraphemes` on `text.toSlice` and
-- copies each slice for the comparison, and a fast counter that counts the slices of the same
-- call without copying."
-- The fast and reference clusters are equal on every input, so comparing outputs cannot show
-- that the fast column runs the scanner. This walk reads the definitions instead: it follows
-- names in `Bench` and `Segmentation` from each fast function and fails unless it reaches
-- `Segmentation.sliceGraphemes`, or if it reaches `clustersOf`, the reference.
open Lean in
theorem fast_column_reaches_sliceGraphemes : True := by
  run_tac do
    let env ← getEnv
    for root in [``Bench.fastClusters, ``Bench.fastClusterCount] do
      let mut seen : NameSet := {}
      let mut todo : Array Name := #[root]
      let mut i := 0
      while i < todo.size do
        let n := todo[i]!
        i := i + 1
        if n == ``Segmentation.clustersOf then
          throwError m!"{root} reaches {n}, the reference segmenter"
        if seen.contains n then continue
        seen := seen.insert n
        if (`Bench).isPrefixOf n then
          match env.find? n with
          | some (.defnInfo info) =>
            for c in info.value.getUsedConstants do
              todo := todo.push c
          | some _ => pure ()
          | none => throwError m!"{n} is missing"
      unless seen.contains ``Segmentation.sliceGraphemes do
        throwError m!"{root} does not call Segmentation.sliceGraphemes"
  trivial
