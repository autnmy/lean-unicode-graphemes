import Segmentation

-- "Do not land an unproved fast path behind a later proof, and do not weaken a statement to make a
-- proof go through."
-- After any ASCII code point the scan state is the same whatever came before: its properties are
-- the ASCII ones and every look-back flag (GB9c, GB11, GB12/GB13) is clear. A state that kept a
-- flag from before the run would join the next non-ASCII code point wrongly.
/-- Pushing ASCII properties onto any state gives the ASCII state, and the ASCII state for a letter
holds that letter's properties with every flag false. -/
theorem push_of_ascii_props_is_ascii_state_with_every_flag_clear :
    (∀ (s : Segmentation.ScanState) (n : Nat),
      s.push (Segmentation.asciiProps n) = Segmentation.asciiState n) ∧
    Segmentation.asciiState 0x61 =
      { prev := Segmentation.asciiProps 0x61, linkerTail := false, pictTail := false,
        zwjAfterPict := false, riOdd := false } :=
  ⟨Segmentation.ScanState.push_asciiProps, rfl⟩
