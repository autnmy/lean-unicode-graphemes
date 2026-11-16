import Lean
import Segmentation

-- "an ASCII fast path: a run of ASCII bytes needs no table lookup except where GB3 (CR LF) or a
-- following non-ASCII code point can join it"
-- Output alone cannot show whether a lookup happened, so this walks the definitions the ASCII
-- decision and the ASCII state reach. The walk starts only from those two, so a table name it
-- meets was reached through their bodies.
open Lean in
/-- The ASCII decision and the ASCII state reach neither the property lookup nor any generated
property table. -/
theorem ascii_path_helpers_read_no_property_table : True := by
  run_tac do
    let env ← getEnv
    let forbidden := [``Segmentation.charProps, ``Segmentation.Tables.propsLookup,
      ``Segmentation.Tables.props]
    let mut seen : NameSet := {}
    let mut todo : Array Name := #[``Segmentation.asciiBreaksBefore, ``Segmentation.asciiState]
    for root in todo do
      unless env.contains root do
        throwError m!"{root} is missing"
    let mut i := 0
    while i < todo.size do
      let n := todo[i]!
      i := i + 1
      if seen.contains n then continue
      seen := seen.insert n
      if forbidden.contains n then
        throwError m!"the ASCII path reaches {n}"
      if (`Segmentation).isPrefixOf n then
        if let some (.defnInfo info) := env.find? n then
          for c in info.value.getUsedConstants do
            todo := todo.push c
  trivial
