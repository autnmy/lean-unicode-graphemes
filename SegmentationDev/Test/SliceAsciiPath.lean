import Segmentation
import SegmentationDev.Gate.Axioms
import SegmentationDev.Test.AsciiBreaksBeforeRules
import SegmentationDev.Test.AsciiStateClearsFlags
import SegmentationDev.Test.SliceAsciiRunReadsNoTable
import SegmentationDev.Test.SliceScannerIssueGuards
import SegmentationDev.Test.SliceAsciiPathHandovers
import SegmentationDev.Test.SliceAsciiRunSubSlice
import SegmentationDev.Test.SliceScanClustersArrayLoop
import SegmentationDev.Test.SliceScanEmitsSlices
import SegmentationDev.Test.SliceFastLookup

/-!
# The scanner's ASCII path and array loop

The modules imported here check the ASCII branch of `Segmentation.scanClusters` and the array it
fills: the ASCII decision against the rules and against `breaksBeforeFast` for every state, the
state it leaves, that it reads no property table, the issue's own guards ("\r\n", "a\r\nb", an
ASCII run then a combining mark, the empty slice), the places where a run meets a non-ASCII code
point or the end of a sub-slice, that the scan and its agreement lemma speak of an `Array`, and
that `sliceGraphemes` has the scan push its slices instead of building cluster bounds first, and
that the scan's block-indexed property lookup equals the whole-table one.
Importing them here makes `lake test` build them. The long run that a loop growing the stack per
cluster would fail is a compiled check in `SegmentationDev.Test`.
-/

-- "every new helper is in the plain-definition check and the axiom gate"
-- `SegmentationDev/Gate/Axioms.lean` holds the gate command, not a list of names, so each new
-- definition and lemma of the scanner, and each agreement theorem re-proved over the new loop, is
-- named in a gate command here.
#assert_axioms Segmentation.asciiBreaksBefore Segmentation.asciiState
  Segmentation.breaksBeforeFast_asciiProps Segmentation.ScanState.push_asciiProps
  Segmentation.scanClusters Segmentation.scanClusters_step Segmentation.clusterBounds
  Segmentation.scanClusters_map Segmentation.mapClusterBounds Segmentation.mapClusterBounds_eq_map
  Segmentation.sliceGraphemes_eq_map Segmentation.sliceBoundaries_eq_map
  Segmentation.scanClusters_agree Segmentation.sliceGraphemes_agree
  Segmentation.graphemes_eq_graphemesFast Segmentation.boundaries_eq_boundariesFast
