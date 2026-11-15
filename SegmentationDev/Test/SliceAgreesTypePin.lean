import Segmentation

-- "`sliceGraphemes_agree` is proved over every `String` with no hypothesis: the clusters read back
-- as strings are exactly `graphemes s`, and the byte cuts are `boundaries s` mapped to byte
-- positions."
-- "The byte position of code-point cut n is the UTF-8 size of the first n code points of `s`."
-- The ascription fails to elaborate if the theorem takes a hypothesis, drops either half, or maps
-- the cuts some other way.
theorem sliceGraphemes_agree_type_states_both_halves_for_every_string : True := by
  have _x : ∀ s : String,
      (Segmentation.sliceGraphemes s.toSlice).map String.Slice.copy = Segmentation.graphemes s ∧
      (Segmentation.sliceBoundaries s.toSlice).map (fun p => p.offset.byteIdx) =
        (Segmentation.boundaries s).map
          (fun n => (String.ofList (s.toList.take n)).utf8ByteSize) :=
    Segmentation.sliceGraphemes_agree
  trivial
