import SegmentationTest.GraphemeBreakTestTheorem

/-!
# Tests of the GraphemeBreakTest.txt theorem

Checks of the generated cases, of the decided check `linesMatch`, and of the link from the
`List Char` core to `graphemes`. Several of these evaluate all 853 cases in the kernel, so, like
`SegmentationTest.GraphemeBreakTestTheorem`, the test driver does not import this file; CI
builds both in its time-limited GraphemeBreakTest.txt step. Check it locally with
`lake build SegmentationTest.GraphemeBreakTestTheoremTests`.
-/

/-! ## The statement -/

-- The statement is pinned here, so a theorem about fewer lines or another function fails to match.
theorem «graphemes matches every one of the 853 lines of GraphemeBreakTest.txt» :
    SegmentationTest.GraphemeBreakTestData.cases.length = 853 ∧
      ∀ c ∈ SegmentationTest.GraphemeBreakTestData.cases,
        SegmentationTest.GraphemeBreakTestLine.clusters c.codePoints = c.expected :=
  SegmentationTest.GraphemeBreakTestTheorem.graphemes_match_graphemeBreakTest

/-! ## The generated cases -/

theorem «the embedded GraphemeBreakTest.txt cases number exactly 853» :
    SegmentationTest.GraphemeBreakTestData.cases.length = 853 := by
  decide +kernel

-- GraphemeBreakTest.txt line 840: ÷ 0061 × 0308 ÷ 0062 ÷
-- The expected clusters come from the file's markers, not from the segmenter.
theorem «the embedded GraphemeBreakTest cases hold line 840 as the file writes it» :
    (SegmentationTest.GraphemeBreakTestData.cases.any fun c =>
      c.line == 840 && c.codePoints == [0x61, 0x308, 0x62]
        && c.expected == [[0x61, 0x308], [0x62]]) = true := by
  decide +kernel

/-! ## The link from the core to `graphemes` -/

-- The kernel decides over the List Char core; this lemma is what makes that a statement about
-- `graphemes`, so it must hold for every input, not only the decided ones.
theorem «the graphemes wrapper and coreClusters agree on every code point list» :
    ∀ cps : List Nat, SegmentationTest.GraphemeBreakTestLine.clusters cps =
      SegmentationTest.GraphemeBreakTestTheorem.coreClusters cps :=
  SegmentationTest.GraphemeBreakTestTheorem.clusters_eq_coreClusters

-- GraphemeBreakTest.txt line 840: ÷ 0061 × 0308 ÷ 0062 ÷
set_option maxRecDepth 20000 in
theorem «coreClusters joins a letter with its combining mark (GraphemeBreakTest.txt line 840)» :
    SegmentationTest.GraphemeBreakTestTheorem.coreClusters [0x61, 0x308, 0x62]
      = [[0x61, 0x308], [0x62]] := by
  decide +kernel

-- Three regional indicators (U+1F1E6 U+1F1E7 U+1F1E8): GB12/GB13 join the first two and break
-- before the third. Astral code points pass through Char.ofNat and back as numbers.
set_option maxRecDepth 20000 in
theorem «coreClusters pairs astral regional indicators into one flag cluster» :
    SegmentationTest.GraphemeBreakTestTheorem.coreClusters [0x1F1E6, 0x1F1E7, 0x1F1E8]
      = [[0x1F1E6, 0x1F1E7], [0x1F1E8]] := by
  decide +kernel

-- GraphemeBreakTest.txt line 840: ÷ 0061 × 0308 ÷ 0062 ÷. The rewrite goes through the lemma,
-- so the result is about `graphemes`, while the kernel only evaluates the List Char core.
set_option maxRecDepth 20000 in
theorem «graphemes clusters a letter with a mark through the proved link to the core» :
    SegmentationTest.GraphemeBreakTestLine.clusters [0x61, 0x308, 0x62] = [[0x61, 0x308], [0x62]] := by
  rw [SegmentationTest.GraphemeBreakTestTheorem.clusters_eq_coreClusters]
  decide +kernel

/-! ## The decided check -/

-- GraphemeBreakTest.txt line 840: ÷ 0061 × 0308 ÷ 0062 ÷, repeated to the file's 853 lines.
set_option maxRecDepth 20000 in
theorem «linesMatch accepts 853 correct lines segmented by coreClusters» :
    SegmentationTest.GraphemeBreakTestTheorem.linesMatch
      SegmentationTest.GraphemeBreakTestTheorem.coreClusters
      (List.replicate 853
        ({ line := 840, codePoints := [0x61, 0x308, 0x62], expected := [[0x61, 0x308], [0x62]] } :
          SegmentationTest.GraphemeBreakTestFile.GraphemeBreakCase)) = true := by
  decide +kernel

-- GraphemeBreakTest.txt line 840: ÷ 0061 × 0308 ÷ 0062 ÷. The count is right (853 cases), so only
-- the cluster comparison can make the check fail here.
set_option maxRecDepth 20000 in
theorem «linesMatch rejects 853 lines when a segmenter that never joins gets them wrong» :
    SegmentationTest.GraphemeBreakTestTheorem.linesMatch (fun cps => cps.map ([·]))
      (List.replicate 853
        ({ line := 840, codePoints := [0x61, 0x308, 0x62], expected := [[0x61, 0x308], [0x62]] } :
          SegmentationTest.GraphemeBreakTestFile.GraphemeBreakCase)) = false := by
  decide +kernel

-- The full case list has the right count, so only the cluster comparison can make this false:
-- a check that ignored mismatches would prove the theorem for any segmenter.
set_option maxRecDepth 20000 in
theorem «linesMatch is false on all 853 cases for a segmenter that never joins code points» :
    SegmentationTest.GraphemeBreakTestTheorem.linesMatch (fun cps => cps.map ([·]))
      SegmentationTest.GraphemeBreakTestData.cases = false := by
  decide +kernel

-- The segmenter here answers each kept line with the file's own expected clusters, so the only
-- thing wrong is that 852 lines are missing.
theorem «linesMatch is false on a truncated case list even when every kept case matches» :
    (let kept := SegmentationTest.GraphemeBreakTestData.cases.take 1
     SegmentationTest.GraphemeBreakTestTheorem.linesMatch
       (fun cps => match kept.find? (fun c => c.codePoints == cps) with
         | some c => c.expected
         | none => [])
       kept) = false := by
  decide +kernel
