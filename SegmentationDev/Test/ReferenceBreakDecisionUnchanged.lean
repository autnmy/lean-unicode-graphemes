import Lean
import Segmentation

-- "`breaksBefore`, `breakRows`, `clustersOf`, `cutsOf`, `graphemes` and `boundaries` stay as
-- they are."
open Lean in
/-- The fast break decision exists, and the reference definitions still decide through the rule
table and never call the fast decision. -/
theorem reference_break_decision_never_reaches_breaksBeforeFast : True := by
  run_tac do
    let env ← getEnv
    unless env.contains ``Segmentation.breaksBeforeFast do
      throwError "Segmentation.breaksBeforeFast is missing"
    let mut seen : NameSet := {}
    let mut todo : Array Name :=
      #[``Segmentation.breaksBefore, ``Segmentation.breakRows, ``Segmentation.clustersOf]
    let mut i := 0
    while i < todo.size do
      let n := todo[i]!
      i := i + 1
      if n == ``Segmentation.breaksBeforeFast then
        throwError "the reference definitions reach Segmentation.breaksBeforeFast"
      if seen.contains n then continue
      seen := seen.insert n
      if (`Segmentation).isPrefixOf n then
        match env.find? n with
        | some (.defnInfo info) =>
          for c in info.value.getUsedConstants do todo := todo.push c
        | _ => pure ()
    -- `breakRows` is one of the walk's roots, so `seen` cannot show that `breaksBefore` reads it;
    -- read `breaksBefore`'s own body instead.
    match env.find? ``Segmentation.breaksBefore with
    | some (.defnInfo info) =>
      unless info.value.getUsedConstants.contains ``Segmentation.breakRows do
        throwError "breaksBefore no longer decides through breakRows"
    | _ => throwError "Segmentation.breaksBefore is not a plain definition"
    let rowNames := Segmentation.breakRows
    let expected := ["GB3", "GB4", "GB5", "GB6", "GB7", "GB8", "GB9", "GB9a", "GB9b", "GB9c",
      "GB11", "GB12, GB13"]
    unless rowNames.map (·.name) == expected do
      throwError "breakRows no longer lists the twelve rules in their order"
  trivial
