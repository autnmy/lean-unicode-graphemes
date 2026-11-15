import Segmentation

open Segmentation in
-- Every code point reads as RI, so GB12/GB13 pair them from the start and the fifth stands alone.
theorem «clustersOf pairs a run of five regional indicators from a stub lookup» :
    (Segmentation.clustersOf (fun _ => { gcb := GCB.RI, extPict := false, incb := InCB.None })
      ['x', 'x', 'x', 'x', 'x'] == [['x', 'x'], ['x', 'x'], ['x']]) = true := by
  decide

open Segmentation in
-- Every code point reads as RI, so GB12/GB13 pair them from the start: cuts after each pair
-- and at the end, counted in code points.
theorem «cutsOf cuts a run of five regional indicators from a stub lookup after each pair» :
    (Segmentation.cutsOf (fun _ => { gcb := GCB.RI, extPict := false, incb := InCB.None })
      ['x', 'x', 'x', 'x', 'x'] == [0, 2, 4, 5]) = true := by
  decide

open Segmentation in
-- With no rule but GB999 applying, every code point is a cluster of its own.
theorem «clustersOf gives one cluster per code point when every code point is Other» :
    (Segmentation.clustersOf (fun _ => { gcb := GCB.Other, extPict := false, incb := InCB.None })
      ['a', 'b', 'c'] == [['a'], ['b'], ['c']]) = true := by
  decide

open Segmentation in
-- With no rule but GB999 applying, every position between code points is a cut, ends included.
theorem «cutsOf gives one cut per code point when every code point is Other» :
    (Segmentation.cutsOf (fun _ => { gcb := GCB.Other, extPict := false, incb := InCB.None })
      ['a', 'b', 'c'] == [0, 1, 2, 3]) = true := by
  decide

/-- Stub lookup for the regional indicator checks: 'R' is RI, 'Z' is ZWJ, anything else is
Other. -/
def graphemesStubRiZwjProps (c : Char) : Segmentation.Props :=
  if c = 'R' then { gcb := .RI, extPict := false, incb := .None }
  else if c = 'Z' then { gcb := .ZWJ, extPict := false, incb := .Extend }
  else { gcb := .Other, extPict := false, incb := .None }

-- "`Segmentation.graphemes : String → List String`, one pass over the input with a small state
-- for GB9c, GB11 and GB12/GB13 (the rules that look further back than one code point)."
-- Mirrors GraphemeBreakTest.txt line 837, `0061 ÷ 1F1E6 × 200D ÷ 1F1E7 × 1F1E8 ÷ 0062`. The ZWJ
-- ends the RI run, so the second RI starts a new pair. A state that kept counting RIs across
-- the ZWJ would join it to the first.
set_option maxRecDepth 20000 in
theorem «clustersOf resets regional indicator parity at a ZWJ inside a flag run (GB12/GB13, GraphemeBreakTest line 837)» :
    Segmentation.clustersOf graphemesStubRiZwjProps ['x', 'R', 'Z', 'R', 'R', 'x'] =
    [['x'], ['R', 'Z'], ['R', 'R'], ['x']] := by
  decide

-- "`Segmentation.boundaries : String → List Nat`, the cut positions counted in code points."
-- Mirrors GraphemeBreakTest.txt line 836, `0061 ÷ 1F1E6 × 1F1E7 × 200D ÷ 1F1E8 ÷ 0062`. The ZWJ
-- joins the pair (GB9) and resets the RI run, so the third RI is cut off.
set_option maxRecDepth 20000 in
theorem «cutsOf breaks after an RI pair even when a ZWJ follows the pair (GB12/GB13, GraphemeBreakTest line 836)» :
    Segmentation.cutsOf graphemesStubRiZwjProps ['x', 'R', 'R', 'Z', 'R', 'x'] =
    [0, 1, 4, 5, 6] := by
  decide
