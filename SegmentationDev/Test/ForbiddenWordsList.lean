import Lean
import SegmentationDev.Gate.KeywordScan

-- "and on any of `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `extern` or
-- `unsafe` in project code."
open Lean in
theorem forbiddenWords_eq_seven_words_in_order : True := by
  run_tac do
    let expected := ["sorry", "admit", "axiom", "native_decide", "implemented_by", "extern", "unsafe"]
    unless SegmentationDev.Gate.forbiddenWords == expected do
      throwError m!"SegmentationDev.Gate.forbiddenWords is {SegmentationDev.Gate.forbiddenWords}"
  trivial
