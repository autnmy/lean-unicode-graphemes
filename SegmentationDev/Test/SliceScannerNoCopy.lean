import Lean
import Segmentation

-- "The scanner uses no `String.toList`, no intermediate `List Char`, no copy of the input, no fuel
-- and no `partial`."
-- Walks every library definition reachable from the two entry points, following only names in
-- `Segmentation` (theorems are not followed, so proofs may still talk about `toList`), and fails
-- if any of them calls a function that turns the input into a `List Char` or a new `String`.
open Lean in
theorem «slice_scanner_reaches_no_toList_ofList_or_copy» : True := by
  run_tac do
    let env ← getEnv
    let forbidden : List Name :=
      [`String.toList, `String.ofList, `String.Slice.copy, `List.asString, `String.mk]
    let mut seen : NameSet := {}
    let mut todo : Array Name := #[`Segmentation.sliceGraphemes, `Segmentation.sliceBoundaries]
    let mut i := 0
    while i < todo.size do
      let n := todo[i]!
      i := i + 1
      if forbidden.contains n then
        throwError m!"the slice scanner reaches {n}, which builds a list or copies the input"
      if seen.contains n then continue
      seen := seen.insert n
      if (`Segmentation).isPrefixOf n then
        match env.find? n with
        | some (.defnInfo info) =>
          for c in info.value.getUsedConstants do
            todo := todo.push c
        | some _ => pure ()
        | none => throwError m!"{n} is missing"
  trivial
