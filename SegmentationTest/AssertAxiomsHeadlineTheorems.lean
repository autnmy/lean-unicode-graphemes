import Segmentation
import Gate.Axioms

-- "The gate passes in CI, and the README says all of the above."
-- The command errors on any axiom outside `propext`, `Classical.choice` and `Quot.sound`, so this
-- file only elaborates when all four headline theorems stay inside that set.
#assert_axioms Segmentation.graphemes_join Segmentation.graphemes_ne_empty
  Segmentation.graphemes_rules Segmentation.boundaries_agree

theorem «assert_axioms accepts the four headline theorems» : True := trivial
