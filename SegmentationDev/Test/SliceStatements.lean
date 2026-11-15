import Lean
import Segmentation

-- "`JoinRestoresInput`, `ClustersNonEmpty`, `CutsMatchRules` and `BoundariesMatchCuts` are proved
-- for `graphemesFast` and `boundariesFast` by the unchanged defs, pinned by type ascriptions in
-- `SegmentationDev/Test/SliceStatements.lean`."
-- `CutsMatchRules` takes `props` before the segmenter, as `Segmentation/Statements.lean` declares
-- its variables, so it is pinned at `Tables.props`. The ascriptions name the committed statement
-- terms, so a theorem proved against a restated or weaker local statement fails here.
open Segmentation in
theorem graphemesFast_boundariesFast_satisfy_committed_statements : True := by
  have _join : Segmentation.JoinRestoresInput Segmentation.graphemesFast :=
    Segmentation.graphemesFast_join
  have _nonEmpty : Segmentation.ClustersNonEmpty Segmentation.graphemesFast :=
    Segmentation.graphemesFast_ne_empty
  have _rules : Segmentation.CutsMatchRules Tables.props Segmentation.graphemesFast :=
    Segmentation.graphemesFast_rules
  have _cuts :
      Segmentation.BoundariesMatchCuts Segmentation.graphemesFast Segmentation.boundariesFast :=
    Segmentation.boundariesFast_agree
  trivial

-- "`@[csimp]` lemmas rewrite `graphemes` to `graphemesFast` and `boundaries` to
-- `boundariesFast`."
-- The two functions are proved equal, so no output check can tell whether the rewrite is
-- registered. This reads the compiler's csimp table instead, and fails if either lemma loses its
-- attribute or rewrites to some other function.
open Lean in
theorem csimp_maps_graphemes_boundaries_to_fast_adapters : True := by
  run_tac do
    let state := Compiler.CSimp.ext.getState (← getEnv)
    for (lemma, reference, fast) in
        [(``Segmentation.graphemes_eq_graphemesFast, ``Segmentation.graphemes,
            ``Segmentation.graphemesFast),
          (``Segmentation.boundaries_eq_boundariesFast, ``Segmentation.boundaries,
            ``Segmentation.boundariesFast)] do
      unless state.thmNames.contains lemma do
        throwError m!"{lemma} is not registered with csimp"
      match state.map.find? reference with
      | some entry =>
        unless entry.toDeclName == fast && entry.thmName == lemma do
          throwError m!"csimp rewrites {reference} to {entry.toDeclName}, not {fast}"
      | none => throwError m!"csimp does not rewrite {reference}"
  trivial

-- "a compiled `#guard` that `graphemes` on "a" U+0301 "b" still returns the right clusters after
-- csimp"
-- `#guard` runs compiled code, so these calls go through the csimp rewrite to the slice scanner.
-- Expected values are literals.
#guard Segmentation.graphemes "a\u0301b" == ["a\u0301", "b"]
#guard Segmentation.boundaries "a\u0301b" == [0, 2, 3]
#guard Segmentation.graphemesFast "" == ([] : List String)
#guard Segmentation.boundariesFast "" == [0]

-- "`Segmentation.boundariesFast (s : String) : List Nat` as the running sums, from 0, of each fast
-- cluster's code-point length."
-- The scanner's own cuts are byte offsets; an adapter that summed those would give [0, 2, 5, 9]
-- here, since U+00E9 is 2 bytes, U+4E2D 3 and U+1F600 4.
#guard Segmentation.boundariesFast (String.ofList ([0x00E9, 0x4E2D, 0x1F600].map Char.ofNat)) ==
  [0, 1, 2, 3]
