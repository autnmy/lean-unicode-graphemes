import Segmentation

open Segmentation in
-- Every code point reads as RI, so GB12/GB13 pair them from the start and the fifth stands alone.
theorem clustersOf_pairs_five_regional_indicators_with_stub_props :
    (Segmentation.clustersOf
        (fun _ => { gcb := GCB.regionalIndicator, extPict := false, incb := InCB.none })
      ['x', 'x', 'x', 'x', 'x'] == [['x', 'x'], ['x', 'x'], ['x']]) = true := by
  decide

open Segmentation in
-- Every code point reads as RI, so GB12/GB13 pair them from the start: cuts after each pair
-- and at the end, counted in code points.
theorem cutsOf_cuts_five_regional_indicators_after_each_pair_with_stub_props :
    (Segmentation.cutsOf
        (fun _ => { gcb := GCB.regionalIndicator, extPict := false, incb := InCB.none })
      ['x', 'x', 'x', 'x', 'x'] == [0, 2, 4, 5]) = true := by
  decide

open Segmentation in
-- With no rule but GB999 applying, every code point is a cluster of its own.
theorem clustersOf_all_other_gives_one_cluster_per_code_point :
    (Segmentation.clustersOf (fun _ => { gcb := GCB.other, extPict := false, incb := InCB.none })
      ['a', 'b', 'c'] == [['a'], ['b'], ['c']]) = true := by
  decide

open Segmentation in
-- With no rule but GB999 applying, every position between code points is a cut, ends included.
theorem cutsOf_all_other_gives_one_cut_per_code_point :
    (Segmentation.cutsOf (fun _ => { gcb := GCB.other, extPict := false, incb := InCB.none })
      ['a', 'b', 'c'] == [0, 1, 2, 3]) = true := by
  decide

/-- Stub lookup for the regional indicator checks: 'R' is RI, 'Z' is ZWJ, anything else is
Other. -/
def graphemesStubRiZwjProps (c : Char) : Segmentation.Props :=
  if c = 'R' then { gcb := .regionalIndicator, extPict := false, incb := .none }
  else if c = 'Z' then { gcb := .zwj, extPict := false, incb := .extend }
  else { gcb := .other, extPict := false, incb := .none }

-- "`Segmentation.graphemes : String → List String`, one pass over the input with a small state
-- for GB9c, GB11 and GB12/GB13 (the rules that look further back than one code point)."
-- Mirrors GraphemeBreakTest.txt line 837, `0061 ÷ 1F1E6 × 200D ÷ 1F1E7 × 1F1E8 ÷ 0062`. The ZWJ
-- ends the RI run, so the second RI starts a new pair. A state that kept counting RIs across
-- the ZWJ would join it to the first.
set_option maxRecDepth 20000 in
theorem clustersOf_resets_regional_indicator_parity_at_zwj_line_837 :
    Segmentation.clustersOf graphemesStubRiZwjProps ['x', 'R', 'Z', 'R', 'R', 'x'] =
    [['x'], ['R', 'Z'], ['R', 'R'], ['x']] := by
  decide

-- "`Segmentation.boundaries : String → List Nat`, the cut positions counted in code points."
-- Mirrors GraphemeBreakTest.txt line 836, `0061 ÷ 1F1E6 × 1F1E7 × 200D ÷ 1F1E8 ÷ 0062`. The ZWJ
-- joins the pair (GB9) and resets the RI run, so the third RI is cut off.
set_option maxRecDepth 20000 in
theorem cutsOf_breaks_after_regional_indicator_pair_before_zwj_line_836 :
    Segmentation.cutsOf graphemesStubRiZwjProps ['x', 'R', 'R', 'Z', 'R', 'x'] =
    [0, 1, 4, 5, 6] := by
  decide
