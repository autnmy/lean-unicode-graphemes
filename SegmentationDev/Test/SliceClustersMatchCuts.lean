import Segmentation

-- "Add `Segmentation/Slice.lean`, imported from `Segmentation.lean`, with
-- `Segmentation.sliceGraphemes (s : String.Slice) : List String.Slice` and
-- `Segmentation.sliceBoundaries (s : String.Slice) : List s.Pos`, both from one internal scan. The
-- cuts include both ends, as `boundaries` does."
-- The running byte sizes of the clusters must be exactly the cuts, starting at 0 and ending at the
-- slice's byte size, so the two outputs describe one scan. The empty slice has no clusters and the
-- single cut 0.
#guard
  let consistent := fun (s : String) =>
    ((Segmentation.sliceGraphemes s.toSlice).map
        (fun g => g.copy.utf8ByteSize)).scanl (· + ·) 0 ==
      (Segmentation.sliceBoundaries s.toSlice).map (fun p => p.offset.byteIdx) &&
    (Segmentation.sliceBoundaries s.toSlice).getLast?.map (fun p => p.offset.byteIdx) ==
      some s.utf8ByteSize
  (Segmentation.sliceGraphemes "".toSlice).isEmpty &&
    (Segmentation.sliceBoundaries "".toSlice).map (fun p => p.offset.byteIdx) == [0] &&
    [String.ofList ([0x1F600, 0x61, 0x0301, 0x0D, 0x0A, 0x1F1E6, 0x1F1E7, 0x20AC].map
        Char.ofNat), "abc", "\r\n"].all consistent
