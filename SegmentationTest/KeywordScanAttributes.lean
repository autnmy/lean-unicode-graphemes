import Lean
import Gate.KeywordScan

-- "A CI step that prints `#print axioms` for each headline theorem (L6, L8) and fails on any axiom
-- outside `propext`, `Classical.choice` and `Quot.sound`, and on any of `sorry`, `admit`, `axiom`,
-- `native_decide`, `implemented_by`, `extern` or `unsafe` in project code."
-- A word placed second in an attribute list, or after a line comment, is still code.
open Lean in
theorem «findForbidden reports extern inside an attribute list and unsafe on later lines» : True := by
  run_tac do
    let source := "@[simp, extern \"c\"] def f : Nat := 0\n-- a note\nunsafe def g : Nat := 1\n@[inline, implemented_by g] def h : Nat := 1"
    let found := Gate.findForbidden source
    unless found == [(1, "extern"), (3, "unsafe"), (4, "implemented_by")] do
      throwError m!"expected extern on line 1, unsafe on line 3, implemented_by on line 4; got {found}"
  trivial
