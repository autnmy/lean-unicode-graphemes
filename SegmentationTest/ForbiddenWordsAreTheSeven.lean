import Lean
import Gate.KeywordScan

-- "Project code uses no `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `extern`
-- or `unsafe`."
open Lean in
theorem «forbiddenWords is exactly the seven words the issue lists» : True := by
  run_tac do
    let expected := ["sorry", "admit", "axiom", "native_decide", "implemented_by", "extern",
      "unsafe"]
    let got := Gate.forbiddenWords
    unless got.length == expected.length && expected.all got.contains do
      throwError m!"forbiddenWords is {got}, expected {expected}"
  trivial
