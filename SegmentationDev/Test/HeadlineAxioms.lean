import SegmentationDev.Gate.Axioms
import Segmentation

/-!
# The axiom gate for the headline theorems

The five theorems the library's claim rests on: the clusters join back to the input
(`JoinRestoresInput`), no cluster is empty (`ClustersNonEmpty`), the segmenter cuts exactly where
UAX #29 says (`CutsMatchRules`), `boundaries` gives the same cuts (`BoundariesMatchCuts`), and the
`String.Slice` scanner gives the same clusters and cuts as `graphemes` and `boundaries`
(`sliceGraphemes_agree`). This is the list the gate checks; the test in
`SegmentationDev/Test/AssertAxiomsPrintsHeadlineAxioms.lean` names the same five to check the
printed output.

`lake test` elaborates this file through the test driver's import. CI also runs
`lake env lean SegmentationDev/Test/HeadlineAxioms.lean`, so the job log shows each theorem's
`#print axioms` output, and the step fails if any theorem depends on an axiom outside
`propext`, `Classical.choice` and `Quot.sound`.
-/

#assert_axioms Segmentation.graphemes_join Segmentation.graphemes_ne_empty
  Segmentation.graphemes_rules Segmentation.boundaries_agree Segmentation.sliceGraphemes_agree
