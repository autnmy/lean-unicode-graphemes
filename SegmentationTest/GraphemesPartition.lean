import Lean
import Segmentation

/-!
Checks of the partition theorems in `Segmentation.Partition`: the clusters of `graphemes` join
back to the input (`H1a`), and no cluster is empty (`H1b`).
-/

-- The type ascriptions pin each theorem to the committed statement applied to the real
-- segmenter, so a theorem that is missing, renamed, or about a weaker statement or a different
-- segmenter fails here.
theorem «graphemes_join is stated as H1a applied to graphemes» :
    Segmentation.H1a Segmentation.graphemes :=
  Segmentation.graphemes_join

theorem «graphemes_ne_empty is stated as H1b applied to graphemes» :
    Segmentation.H1b Segmentation.graphemes :=
  Segmentation.graphemes_ne_empty

-- H1a must hold for every string, including the empty one and text that splits into several
-- clusters (a base letter with a combining mark, then CR LF, then a letter).
theorem «graphemes_join gives back a multi-cluster string with combining mark and CRLF» :
    String.join (Segmentation.graphemes "") = "" ∧
      String.join (Segmentation.graphemes "e\u0301\r\nx") = "e\u0301\r\nx" :=
  ⟨Segmentation.graphemes_join "", Segmentation.graphemes_join "e\u0301\r\nx"⟩

-- A text that starts with a combining mark, then a lone CR, then CR LF exercises the break rules
-- most likely to drop or duplicate a code point.
theorem «graphemes_join covers a lone CR before CRLF and a combining mark» :
    String.join (Segmentation.graphemes "\u0301\r\r\na\u200D") = "\u0301\r\r\na\u200D" :=
  Segmentation.graphemes_join "\u0301\r\r\na\u200D"

-- The empty string never appears among the clusters of a text made of several clusters.
theorem «graphemes_ne_empty rules out an empty first cluster» :
    "" ∉ Segmentation.graphemes "e\u0301\r\nx" :=
  fun h => Segmentation.graphemes_ne_empty "e\u0301\r\nx" "" h rfl

-- The empty text and a text that ends with a lone CR are where an empty trailing cluster would
-- appear.
theorem «graphemes_ne_empty rules out an empty cluster for the empty string and a lone CR» :
    (∀ g ∈ Segmentation.graphemes "", g ≠ "") ∧ (∀ g ∈ Segmentation.graphemes "a\r", g ≠ "") :=
  ⟨Segmentation.graphemes_ne_empty "", Segmentation.graphemes_ne_empty "a\r"⟩

-- `#print axioms` only prints, so these read the same axiom list and fail on anything beyond
-- `propext`, `Classical.choice` and `Quot.sound`. A proof by `sorry` depends on `sorryAx`,
-- which is not in the allowed list.
open Lean in
theorem «graphemes_join uses no sorry and no axiom beyond propext, Classical.choice and Quot.sound» :
    True := by
  run_tac do
    let used ← collectAxioms ``Segmentation.graphemes_join
    let allowed := [``propext, ``Classical.choice, ``Quot.sound]
    for ax in used do
      unless allowed.contains ax do
        throwError m!"Segmentation.graphemes_join depends on the disallowed axiom {ax}"
  trivial

open Lean in
theorem «graphemes_ne_empty uses no sorry and no axiom beyond propext, Classical.choice and Quot.sound» :
    True := by
  run_tac do
    let used ← collectAxioms ``Segmentation.graphemes_ne_empty
    let allowed := [``propext, ``Classical.choice, ``Quot.sound]
    for ax in used do
      unless allowed.contains ax do
        throwError m!"Segmentation.graphemes_ne_empty depends on the disallowed axiom {ax}"
  trivial
