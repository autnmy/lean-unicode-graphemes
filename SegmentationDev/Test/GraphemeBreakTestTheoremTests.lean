import SegmentationDev.Test.GraphemeBreakTestTheorem

/-!
# Tests of the GraphemeBreakTest.txt theorem

Checks of the generated cases, of the decided check `linesMatch`, and of the link from the
`List Char` core to `graphemes`. Several of these evaluate all 853 cases in the kernel, so, like
`SegmentationDev.Test.GraphemeBreakTestTheorem`, the test driver does not import this file; CI
builds both in its time-limited GraphemeBreakTest.txt step. Check it locally with
`lake build SegmentationDev.Test.GraphemeBreakTestTheoremTests`.
-/

/-! ## The statement -/

-- The statement is pinned here, so a theorem about fewer lines or another function fails to match.
theorem graphemes_match_all_853_graphemeBreakTest_lines :
    SegmentationDev.Test.GraphemeBreakTestData.cases.length = 853 ∧
      ∀ c ∈ SegmentationDev.Test.GraphemeBreakTestData.cases,
        SegmentationDev.Test.GraphemeBreakTestLine.clusters c.codePoints = c.expected :=
  SegmentationDev.Test.GraphemeBreakTestTheorem.graphemes_match_graphemeBreakTest

/-! ## The generated cases -/

theorem graphemeBreakTest_cases_length_eq_853 :
    SegmentationDev.Test.GraphemeBreakTestData.cases.length = 853 := by
  decide +kernel

-- GraphemeBreakTest.txt line 840: ÷ 0061 × 0308 ÷ 0062 ÷
-- The expected clusters come from the file's markers, not from the segmenter.
theorem graphemeBreakTest_cases_hold_line_840_as_written :
    (SegmentationDev.Test.GraphemeBreakTestData.cases.any fun c =>
      c.line == 840 && c.codePoints == [0x61, 0x308, 0x62]
        && c.expected == [[0x61, 0x308], [0x62]]) = true := by
  decide +kernel

/-! ## The link from the core to `graphemes` -/

-- The kernel decides over the List Char core; this lemma is what makes that a statement about
-- `graphemes`, so it must hold for every input, not only the decided ones.
theorem graphemeBreakTest_clusters_eq_coreClusters_for_every_list :
    ∀ cps : List Nat, SegmentationDev.Test.GraphemeBreakTestLine.clusters cps =
      SegmentationDev.Test.GraphemeBreakTestTheorem.coreClusters cps :=
  SegmentationDev.Test.GraphemeBreakTestTheorem.clusters_eq_coreClusters

-- GraphemeBreakTest.txt line 840: ÷ 0061 × 0308 ÷ 0062 ÷
set_option maxRecDepth 20000 in
theorem coreClusters_joins_letter_with_mark_line_840 :
    SegmentationDev.Test.GraphemeBreakTestTheorem.coreClusters [0x61, 0x308, 0x62]
      = [[0x61, 0x308], [0x62]] := by
  decide +kernel

-- Three regional indicators (U+1F1E6 U+1F1E7 U+1F1E8): GB12/GB13 join the first two and break
-- before the third. Astral code points pass through Char.ofNat and back as numbers.
set_option maxRecDepth 20000 in
theorem coreClusters_pairs_astral_regional_indicators :
    SegmentationDev.Test.GraphemeBreakTestTheorem.coreClusters [0x1F1E6, 0x1F1E7, 0x1F1E8]
      = [[0x1F1E6, 0x1F1E7], [0x1F1E8]] := by
  decide +kernel

-- GraphemeBreakTest.txt line 840: ÷ 0061 × 0308 ÷ 0062 ÷. The rewrite goes through the lemma,
-- so the result is about `graphemes`, while the kernel only evaluates the List Char core.
set_option maxRecDepth 20000 in
theorem graphemeBreakTest_clusters_letter_with_mark_via_core_link :
    SegmentationDev.Test.GraphemeBreakTestLine.clusters [0x61, 0x308, 0x62] = [[0x61, 0x308], [0x62]] := by
  rw [SegmentationDev.Test.GraphemeBreakTestTheorem.clusters_eq_coreClusters]
  decide +kernel

/-! ## The decided check -/

-- GraphemeBreakTest.txt line 840: ÷ 0061 × 0308 ÷ 0062 ÷, repeated to the file's 853 lines.
set_option maxRecDepth 20000 in
theorem linesMatch_coreClusters_accepts_853_correct_lines :
    SegmentationDev.Test.GraphemeBreakTestTheorem.linesMatch
      SegmentationDev.Test.GraphemeBreakTestTheorem.coreClusters
      (List.replicate 853
        ({ line := 840, codePoints := [0x61, 0x308, 0x62], expected := [[0x61, 0x308], [0x62]] } :
          SegmentationDev.Test.GraphemeBreakTestFile.GraphemeBreakCase)) = true := by
  decide +kernel

-- GraphemeBreakTest.txt line 840: ÷ 0061 × 0308 ÷ 0062 ÷. The count is right (853 cases), so only
-- the cluster comparison can make the check fail here.
set_option maxRecDepth 20000 in
theorem linesMatch_never_joining_rejects_853_wrong_lines :
    SegmentationDev.Test.GraphemeBreakTestTheorem.linesMatch (fun cps => cps.map ([·]))
      (List.replicate 853
        ({ line := 840, codePoints := [0x61, 0x308, 0x62], expected := [[0x61, 0x308], [0x62]] } :
          SegmentationDev.Test.GraphemeBreakTestFile.GraphemeBreakCase)) = false := by
  decide +kernel

-- The full case list has the right count, so only the cluster comparison can make this false:
-- a check that ignored mismatches would prove the theorem for any segmenter.
set_option maxRecDepth 20000 in
theorem linesMatch_never_joining_false_on_all_853_cases :
    SegmentationDev.Test.GraphemeBreakTestTheorem.linesMatch (fun cps => cps.map ([·]))
      SegmentationDev.Test.GraphemeBreakTestData.cases = false := by
  decide +kernel

-- The segmenter here answers each kept line with the file's own expected clusters, so the only
-- thing wrong is that 852 lines are missing.
theorem linesMatch_false_on_truncated_case_list :
    (let kept := SegmentationDev.Test.GraphemeBreakTestData.cases.take 1
     SegmentationDev.Test.GraphemeBreakTestTheorem.linesMatch
       (fun cps => match kept.find? (fun c => c.codePoints == cps) with
         | some c => c.expected
         | none => [])
       kept) = false := by
  decide +kernel
