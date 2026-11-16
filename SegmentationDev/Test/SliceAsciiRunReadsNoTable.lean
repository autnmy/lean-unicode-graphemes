import Lean
import Segmentation

-- "A run of ASCII bytes needs no table lookup except where GB3 (CR LF) or a following non-ASCII
-- code point can join it."
-- Output is the same with or without a lookup, so only a walk over definition bodies can see it.
-- The scan must reach the ASCII decision and state, and those two must reach neither a property
-- lookup nor the general decision and push. Neither asserted name is a root of the walk it is
-- asserted in, so the check cannot pass by seeding.
open Lean in
/-- The scan uses the ASCII decision and state, and those reach no property table, no general break decision and no state push. -/
theorem slice_ascii_run_decides_without_table_lookup : True := by
  run_tac do
    let env ← getEnv
    let reach (roots : Array Name) : NameSet := Id.run do
      let mut seen : NameSet := {}
      let mut todo := roots
      let mut i := 0
      while i < todo.size do
        let n := todo[i]!
        i := i + 1
        if seen.contains n then continue
        seen := seen.insert n
        if (`Segmentation).isPrefixOf n then
          if let some (.defnInfo info) := env.find? n then
            for c in info.value.getUsedConstants do
              todo := todo.push c
      return seen
    let fromScan := reach #[``Segmentation.scanClusters]
    for helper in [``Segmentation.asciiBreaksBefore, ``Segmentation.asciiState] do
      unless fromScan.contains helper do
        throwError m!"Segmentation.scanClusters does not reach {helper}"
    let fromRun := reach #[``Segmentation.asciiBreaksBefore, ``Segmentation.asciiState]
    for slow in [``Segmentation.charProps, ``Segmentation.Tables.propsLookup,
        ``Segmentation.Tables.props, ``Segmentation.breaksBeforeFast,
        ``Segmentation.ScanState.push] do
      if fromRun.contains slow then
        throwError m!"the ASCII decision or state reaches {slow}"
  trivial
