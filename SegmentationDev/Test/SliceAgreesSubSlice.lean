import Segmentation
import SegmentationDev.Test.SliceAgreesEdgeInputs

/-!
# The slice scanner on a sub-slice from the middle of a string

The headline theorem `sliceGraphemes_agree` is stated over `s.toSlice`. The lemma under it,
`sliceGraphemes_agree_clustersOf`, holds on any slice, a slice that starts after byte 0 included:
the clusters read back as `clustersOf` on the slice's text, and the cuts are byte offsets from the
slice start. These compiled checks run that case: expected values come from the reference on the
sub-slice's own text, plus the literal cuts, so a scan that measures from the parent's start fails.
-/

-- "A sub-slice taken from the middle of a larger string must return slices of that sub-slice and
-- cuts measured from its start."
-- Both parents start with U+00E9 (2 bytes), so each sub-slice starts at byte 2 of its parent, and
-- each sub-slice ends on a CR with the parent's LF just past its end. A scanner that reads past the
-- slice end joins CR with that LF (GB3); one that measures from the parent's start gives cuts
-- shifted by 2. The first sub-slice also holds a non-ASCII extender, U+0301.
#guard
  let parent := sliceTestText [0x00E9, 0x78, 0x0301, 0x0D, 0x0A, 0x7A]
  let sub := (parent.toSlice.drop 1).dropEnd 2
  sub.copy == "x\u0301\r" &&
    sliceAgreesWithReference sub &&
    (Segmentation.sliceGraphemes sub).map String.Slice.copy == ["x\u0301", "\r"] &&
    (Segmentation.sliceBoundaries sub).map (fun p => p.offset.byteIdx) == [0, 3, 4]

#guard
  let parent := sliceTestText [0x00E9, 0x78, 0x61, 0x0D, 0x0A, 0x62]
  let sub := (parent.toSlice.drop 1).take 3
  sub.copy == "xa\r" &&
    sliceAgreesWithReference sub &&
    (Segmentation.sliceGraphemes sub).map String.Slice.copy == ["x", "a", "\r"] &&
    (Segmentation.sliceBoundaries sub).map (fun p => p.offset.byteIdx) == [0, 1, 2, 3]
