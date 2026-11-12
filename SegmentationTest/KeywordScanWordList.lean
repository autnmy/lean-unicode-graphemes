import Lean
import Gate.KeywordScan

-- "Project code uses no `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `extern` or `unsafe`."
-- A word dropped from the list would let it into project code without the scan noticing.
open Lean in
theorem «forbiddenWords holds exactly the seven words the issue lists» : True := by
  run_tac do
    let expected := ["sorry", "admit", "axiom", "native_decide", "implemented_by", "extern", "unsafe"]
    let words := Gate.forbiddenWords
    unless words.length == expected.length && expected.all words.contains do
      throwError m!"expected {expected}, got {words}"
  trivial
