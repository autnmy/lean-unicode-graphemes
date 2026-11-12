import Gate.Axioms
import Segmentation

/-!
# The axiom gate for the headline theorems

The four theorems the README cites as the library's claim: the clusters join back to the input
(`H1a`), no cluster is empty (`H1b`), the segmenter cuts exactly where UAX #29 says (`H2`), and
`boundaries` gives the same cuts (`H2'`). This is the list the gate checks; the test in
`SegmentationTest/AssertAxiomsPrintsHeadlineAxioms.lean` names the same four to check the printed
output.

`lake test` elaborates this file through the test driver's import. CI also runs
`lake env lean SegmentationTest/HeadlineAxioms.lean`, so the job log shows each theorem's
`#print axioms` output, and the step fails if any theorem depends on an axiom outside
`propext`, `Classical.choice` and `Quot.sound`.
-/

#assert_axioms Segmentation.graphemes_join Segmentation.graphemes_ne_empty
  Segmentation.graphemes_rules Segmentation.boundaries_agree
