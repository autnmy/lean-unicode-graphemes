import Lean
import Segmentation

-- "Compiled code builds the table once as a closed term."
-- A top-level constant with no parameters is evaluated once when compiled code starts. If the
-- table took an argument, or `propsLookup` merged the source tables in its own body instead of
-- naming `propsRanges`, the merge would run again on every call.
open Lean in
theorem «propsRanges is a closed constant that propsLookup reads instead of rebuilding the table per call» :
    True := by
  run_tac do
    let env ← getEnv
    match env.find? ``Segmentation.Tables.propsRanges with
    | some (.defnInfo info) =>
      if info.type.isForall then
        throwError m!"propsRanges takes arguments, so it is not a closed term: {info.type}"
    | _ => throwError "propsRanges is not a definition"
    match env.find? ``Segmentation.Tables.propsLookup with
    | some (.defnInfo info) =>
      let consts := info.value.getUsedConstants
      unless consts.contains ``Segmentation.Tables.propsRanges do
        throwError "propsLookup does not read the closed table propsRanges"
      if consts.contains ``Segmentation.Tables.Range.mergeWith then
        throwError "propsLookup merges the tables on every call"
    | _ => throwError "propsLookup is not a definition"
  trivial
