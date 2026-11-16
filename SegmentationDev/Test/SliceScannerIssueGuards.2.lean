import Segmentation

-- "Add `#guard` checks: \"\\r\\n\" is one cluster, \"a\\r\\nb\" is three clusters, an ASCII run
-- followed by a combining mark keeps the mark on the last letter, and an empty slice gives `[]`."
-- Expected values are literals, never `graphemes`, which `@[csimp]` turns into the scanner.
-- The four cases the issue names, each checked by cluster count and contents, through
-- `sliceGraphemes` and through the cluster bounds array the loop builds. A `#guard` runs the
-- compiled scanner without the extra axiom a compiled-evaluation proof would add.
#guard
  (Segmentation.sliceGraphemes "\r\n".toSlice).map String.Slice.copy == ["\r\n"] &&
    (Segmentation.clusterBounds "\r\n".toSlice).size == 1 &&
    (Segmentation.sliceGraphemes "a\r\nb".toSlice).map String.Slice.copy == ["a", "\r\n", "b"] &&
    (Segmentation.clusterBounds "a\r\nb".toSlice).size == 3 &&
    (Segmentation.sliceGraphemes "xya\u0301".toSlice).map String.Slice.copy ==
      ["x", "y", "a\u0301"] &&
    (Segmentation.clusterBounds "xya\u0301".toSlice).size == 3 &&
    (Segmentation.sliceGraphemes "".toSlice).isEmpty &&
    (Segmentation.clusterBounds "".toSlice).size == 0 &&
    (Segmentation.sliceBoundaries "".toSlice).map (fun p => p.offset.byteIdx) == [0]
