import SegmentationDev.Gate.Axioms
import SegmentationDev.Test.GraphemeBreakTestData
import SegmentationDev.Test.GraphemeBreakTestLine

/-!
# GraphemeBreakTest.txt as a theorem

States that `Segmentation.graphemes` gives the clusters Unicode's conformance file expects on
every one of its 853 test lines, and proves it with `decide +kernel`, so the Lean kernel checks
each line rather than the compiled code. `lake test` runs the same comparison at run time by
reading the file; this is the proved form of that check.

The cases come from `SegmentationDev.Test.GraphemeBreakTestData`, which `lake exe gen-tables`
writes from the file; `lake test` and CI fail when it differs from what the file gives.

The kernel decides the comparison over the `List Char` core, `clustersOf`, because going through
`String` would spend most of its time on UTF-8 encoding. `clusters_eq_coreClusters` proves that
this is the same as asking `graphemes`, for every input.

The test driver does not import this module, because CI checks it in a step of its own with a
time limit. Check it locally with `lake build SegmentationDev.Test.GraphemeBreakTestTheorem`.
-/

namespace SegmentationDev.Test.GraphemeBreakTestTheorem

open SegmentationDev.Test.GraphemeBreakTestFile

/-- The clusters of the code points `cps` by the `List Char` core with the generated tables,
each as its code point numbers. -/
def coreClusters (cps : List Nat) : List (List Nat) :=
  (Segmentation.clustersOf Segmentation.Tables.props (cps.map Char.ofNat)).map
    (·.map Char.toNat)

/-- Whether `segment` gets every case of `cases` right and there are exactly 853 of them. The
count is part of the check so that a shorter list cannot pass for the whole file. -/
def linesMatch (segment : List Nat → List (List Nat)) (cases : List GraphemeBreakCase) : Bool :=
  cases.length == expectedLineCount && (mismatches segment cases).isEmpty

/-- The `graphemes` wrapper the runtime check uses gives the same clusters as the core. -/
theorem clusters_eq_coreClusters (cps : List Nat) :
    GraphemeBreakTestLine.clusters cps = coreClusters cps := by
  simp [GraphemeBreakTestLine.clusters, GraphemeBreakTestLine.text, coreClusters,
    Segmentation.graphemes, String.toList_ofList, Function.comp_def]

/-- What `linesMatch` checks, as a proposition about each case. -/
theorem linesMatch_spec {segment : List Nat → List (List Nat)} {cases : List GraphemeBreakCase}
    (h : linesMatch segment cases = true) :
    cases.length = 853 ∧ ∀ c ∈ cases, segment c.codePoints = c.expected := by
  simp only [linesMatch, Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff, mismatches,
    List.filterMap_eq_nil_iff] at h
  exact ⟨h.1, fun c hc => by simpa using h.2 c hc⟩

/-- The core gives the expected clusters on all 853 lines, checked by the kernel. -/
theorem coreClusters_match_graphemeBreakTest :
    linesMatch coreClusters GraphemeBreakTestData.cases = true := by
  decide +kernel

/-- `graphemes` gives the clusters GraphemeBreakTest.txt expects on every one of its 853 test
lines. -/
theorem graphemes_match_graphemeBreakTest :
    GraphemeBreakTestData.cases.length = 853 ∧
      ∀ c ∈ GraphemeBreakTestData.cases,
        GraphemeBreakTestLine.clusters c.codePoints = c.expected := by
  have h := linesMatch_spec coreClusters_match_graphemeBreakTest
  exact ⟨h.1, fun c hc => (clusters_eq_coreClusters _).trans (h.2 c hc)⟩

/-! ## The check can fail -/

-- GraphemeBreakTest.txt line 840: ÷ 0061 × 0308 ÷ 0062 ÷. A segmenter that never joins splits
-- the letter from its mark, so the comparison must report this line.
theorem mismatches_never_joining_segmenter_eq_line_840 :
    mismatches (fun cps => cps.map ([·]))
      [.ofClusters 840 [[0x61, 0x308], [0x62]]] = [840] := by
  decide +kernel

-- With no cases nothing is compared, so the count check alone must make this false.
theorem linesMatch_nil_eq_false :
    linesMatch coreClusters [] = false := by
  decide +kernel

end SegmentationDev.Test.GraphemeBreakTestTheorem

#assert_axioms SegmentationDev.Test.GraphemeBreakTestTheorem.graphemes_match_graphemeBreakTest
