import Lean
import Segmentation

-- "ASCII bytes are read without a table lookup and each non-ASCII code point does one lookup in
-- the combined table."
-- No test can count lookups at run time, so this reads the definitions: `charProps` must use
-- `asciiProps` and the combined `propsLookup`, and never the three separate lookups behind
-- `Tables.props`; `asciiProps`, and every library definition it reaches, must read no table.
open Lean in
theorem «charProps_reads_asciiProps_or_one_combined_lookup_and_asciiProps_reads_no_table» :
    True := by
  run_tac do
    let env ← getEnv
    let threeLookups : List Name :=
      [`Segmentation.Tables.props, `Segmentation.Tables.gcbOf, `Segmentation.Tables.extPictOf,
        `Segmentation.Tables.incbOf]
    match env.find? `Segmentation.charProps with
    | some (.defnInfo info) =>
      let cs := info.value.getUsedConstants
      unless cs.contains `Segmentation.asciiProps do
        throwError "charProps does not take ASCII properties from asciiProps"
      unless cs.contains `Segmentation.Tables.propsLookup do
        throwError "charProps does not read non-ASCII properties from the combined propsLookup"
      for n in threeLookups do
        if cs.contains n then
          throwError m!"charProps calls {n}, a lookup other than the combined table"
    | _ => throwError "charProps is not a definition"
    let tables : List Name := threeLookups ++
      [`Segmentation.Tables.propsLookup, `Segmentation.Tables.propsRanges,
        `Segmentation.Tables.Range.lookup]
    let mut seen : NameSet := {}
    let mut todo : Array Name := #[`Segmentation.asciiProps]
    let mut i := 0
    while i < todo.size do
      let n := todo[i]!
      i := i + 1
      if tables.contains n then
        throwError m!"asciiProps reaches {n}, so ASCII code points still read a table"
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
