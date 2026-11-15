import Lean
import Segmentation

-- "`graphemesFast` and `boundariesFast` are computed from `sliceGraphemes` output and do not call
-- `graphemes` or `boundaries`."
-- Walks every library definition reachable from each adapter, following only names in
-- `Segmentation` (theorems are not followed), and fails if any of them uses the reference
-- segmenter or its list core, or if the walk never reaches `sliceGraphemes`. A type pin cannot
-- catch this: an adapter defined as `graphemes s` satisfies every pin.
open Lean in
theorem «graphemesFast and boundariesFast reach no reference segmenter» : True := by
  run_tac do
    let env ← getEnv
    let reference : List Name :=
      [``Segmentation.graphemes, ``Segmentation.boundaries, ``Segmentation.clustersOf,
        ``Segmentation.cutsOf]
    for start in [``Segmentation.graphemesFast, ``Segmentation.boundariesFast] do
      let mut seen : NameSet := {}
      let mut todo : Array Name := #[start]
      let mut i := 0
      while i < todo.size do
        let n := todo[i]!
        i := i + 1
        if reference.contains n then
          throwError m!"{start} reaches {n}, the reference segmenter"
        if seen.contains n then continue
        seen := seen.insert n
        if (`Segmentation).isPrefixOf n then
          match env.find? n with
          | some (.defnInfo info) =>
            for c in info.value.getUsedConstants do
              todo := todo.push c
          | some _ => pure ()
          | none => throwError m!"{n} is missing"
      unless seen.contains ``Segmentation.sliceGraphemes do
        throwError m!"{start} is not computed from Segmentation.sliceGraphemes"
  trivial
