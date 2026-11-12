import Lean
import Segmentation
import Gate.Axioms

-- "The gate passes in CI, and the README says all of the above."
-- The four headline theorems (H1a, H1b, H2, H2') rest only on the allowed axioms, so the
-- command elaborates without error; an error here stops this file.
#assert_axioms Segmentation.graphemes_join Segmentation.graphemes_ne_empty Segmentation.graphemes_rules Segmentation.boundaries_agree

theorem «assert_axioms accepts the four headline theorems» : True := trivial
