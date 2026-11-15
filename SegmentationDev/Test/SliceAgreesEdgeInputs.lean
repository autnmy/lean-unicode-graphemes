import Lean
import Segmentation

-- "Compiled `#guard` checks that the clusters (copied) equal `graphemes` and the byte cuts equal
-- mapped `boundaries` on: "", "abc", "\\r\\n", "\\r" then U+0301, "a" then U+0301, "a" then
-- U+200D, a string ending in "\\r", "x" then two Regional Indicators, ASCII between two emoji ZWJ
-- sequences, a string of only non-ASCII, multi-byte code points at the start and the end, and
-- "\\r\\n" right where an ASCII run meets a non-ASCII code point."
-- The `#guard` runs compiled code, so it checks the scanner as it executes, not only its proof.
-- The expected cuts come only from `boundaries` and `String.toList`, never from the scanner.
open Lean Elab Command in
theorem «slice_scanner_agrees_with_reference_on_listed_edge_inputs» : True := by
  run_tac do
    let saved := (← getThe Core.State).messages
    liftCommandElabM (elabCommand (← `(command|
      #guard
        let agrees := fun (s : String) =>
          (Segmentation.sliceGraphemes s.toSlice).map String.Slice.copy ==
              Segmentation.graphemes s &&
            (Segmentation.sliceBoundaries s.toSlice).map (fun p => p.offset.byteIdx) ==
              (Segmentation.boundaries s).map
                (fun n => (String.ofList (s.toList.take n)).utf8ByteSize)
        let text := fun (cps : List Nat) => String.ofList (cps.map Char.ofNat)
        ["", "abc", "\r\n", "\r\u0301", "a\u0301", "a\u200D", "ab\r",
          text [0x78, 0x1F1E6, 0x1F1E7],
          text [0x1F469, 0x200D, 0x1F4BB, 0x61, 0x62, 0x1F468, 0x200D, 0x1F373],
          text [0x00E9, 0x0915, 0x094D, 0x0937, 0x20AC, 0x1F600],
          text [0x1F600, 0x61, 0x62, 0x00E9, 0x20AC],
          text [0x61, 0x62, 0x0D, 0x0A, 0x00E9, 0x63]].all agrees)))
    let failed := (← getThe Core.State).messages.hasErrors
    modifyThe Core.State fun s => { s with messages := saved }
    if failed then
      throwError "the slice scanner disagrees with graphemes or boundaries on a listed input"
  trivial
