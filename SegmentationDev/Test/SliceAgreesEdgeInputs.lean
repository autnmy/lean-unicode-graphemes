import Segmentation

/-!
# The slice scanner agrees with the reference on the ASCII path's edge inputs

Every check here runs compiled code, so it checks the scanner as it executes, not only its proof.
Expected values come only from `graphemes`, `boundaries` and `String.toList`, never from the
scanner. Code points above U+FFFF are written as `Nat` lists, since a `\u` escape takes exactly
four hex digits.
-/

/-- Whether the scanner agrees with the reference on `s`: its clusters, copied, are `graphemes` of
the text of `s`, and its cuts, as byte offsets from the start of `s`, are `boundaries` mapped to
the UTF-8 size of the first n code points. -/
def sliceAgreesWithReference (s : String.Slice) : Bool :=
  let text := s.copy
  (Segmentation.sliceGraphemes s).map String.Slice.copy == Segmentation.graphemes text &&
    (Segmentation.sliceBoundaries s).map (fun p => p.offset.byteIdx) ==
      (Segmentation.boundaries text).map
        (fun n => (String.ofList (text.toList.take n)).utf8ByteSize)

/-- The text with the code points `cps`. -/
def sliceTestText (cps : List Nat) : String := String.ofList (cps.map Char.ofNat)

-- "Compiled `#guard` checks that the clusters (copied) equal `graphemes` and the byte cuts equal
-- mapped `boundaries` on: "", "abc", "\\r\\n", "\\r" then U+0301, "a" then U+0301, "a" then
-- U+200D, a string ending in "\\r", "x" then two Regional Indicators, ASCII between two emoji ZWJ
-- sequences, a string of only non-ASCII, multi-byte code points at the start and the end, and
-- "\\r\\n" right where an ASCII run meets a non-ASCII code point."
#guard ["", "abc", "\r\n", "\r\u0301", "a\u0301", "a\u200D", "ab\r",
    sliceTestText [0x78, 0x1F1E6, 0x1F1E7],
    sliceTestText [0x1F469, 0x200D, 0x1F4BB, 0x61, 0x62, 0x1F468, 0x200D, 0x1F373],
    sliceTestText [0x00E9, 0x0915, 0x094D, 0x0937, 0x20AC, 0x1F600],
    sliceTestText [0x1F600, 0x61, 0x62, 0x00E9, 0x20AC],
    sliceTestText [0x61, 0x62, 0x0D, 0x0A, 0x00E9, 0x63]].all
  fun s => sliceAgreesWithReference s.toSlice

-- "The byte position of code-point cut n is the UTF-8 size of the first n code points of `s`."
-- U+00E9 is 2 bytes, U+4E2D is 3 bytes and U+1F600 is 4 bytes. A scanner that steps one byte per
-- code point, or reports code-point counts, or treats a continuation byte as ASCII, gives different
-- cuts. Two inputs put CR LF right where an ASCII run meets a non-ASCII code point.
#guard [[0x00E9, 0x4E2D, 0x1F600], [0x1F600, 0x61, 0x62, 0x00E9], [0x61, 0x62, 0x0D, 0x0A, 0x4E2D],
    [0x4E2D, 0x0D, 0x0A, 0x61]].all
  fun cps => sliceAgreesWithReference (sliceTestText cps).toSlice

#guard (Segmentation.sliceBoundaries (sliceTestText [0x00E9, 0x4E2D, 0x1F600]).toSlice).map
    (fun p => p.offset.byteIdx) == [0, 2, 5, 9]

-- "an ASCII fast path: a run of ASCII bytes needs no table lookup except where GB3 (CR LF) or a
-- following non-ASCII code point can join it"
-- A fast path that cuts after every ASCII code point except CR before LF splits "a" from U+0301
-- (Extend), U+200D (ZWJ) and U+0903 (SpacingMark). Each input must give exactly the reference's
-- clusters and byte cuts, and its last cluster must be the extender joined to the ASCII code point
-- just before it.
#guard [[0x61, 0x0301], [0x61, 0x200D], [0x61, 0x0903], [0x78, 0x79, 0x61, 0x0301]].all fun cps =>
  let s := sliceTestText cps
  sliceAgreesWithReference s.toSlice &&
    (Segmentation.sliceGraphemes s.toSlice).getLast?.map String.Slice.copy ==
      some (sliceTestText (cps.drop (cps.length - 2)))

-- "The scanner reuses `ScanState`, `ScanState.start`, `ScanState.push` and `breaksBefore` from
-- `Segmentation/Graphemes.lean` unchanged."
-- If the ASCII path skips pushing its code points into the scan state, flags from before the run
-- survive it: U+1F469 U+200D leaves the GB11 flag set, so "a" then U+1F469 would wrongly join; and
-- an odd regional indicator before "a" would wrongly pair the next two indicators differently.
#guard [[0x1F469, 0x200D, 0x61, 0x1F469],
    [0x1F469, 0x200D, 0x1F469, 0x61, 0x62, 0x1F469, 0x200D, 0x1F469],
    [0x1F1E6, 0x61, 0x1F1E7, 0x1F1E8]].all
  fun cps => sliceAgreesWithReference (sliceTestText cps).toSlice
