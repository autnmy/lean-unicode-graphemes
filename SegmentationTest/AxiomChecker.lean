import Gate.Axioms
import Segmentation

/-!
Checks of `#assert_axioms` in `Gate.Axioms`. The axiom subset decision itself, `disallowedAxioms`,
is checked by the files that test it directly; these checks cover the command around it.
-/

-- A misspelled or renamed theorem must fail the check instead of dropping out of it.
/-- error: Unknown constant `Segmentation.graphemes_jion` -/
#guard_msgs in
#assert_axioms Segmentation.graphemes_jion

-- A lemma that uses only allowed axioms passes. Its printed axiom list is dropped rather than
-- matched, so a proof that later needs fewer axioms does not break this check.
#guard_msgs (drop info) in
#assert_axioms Segmentation.isBoundary_zero
