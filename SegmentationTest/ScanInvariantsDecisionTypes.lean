import Segmentation

open Segmentation

-- "Ascribe every lemma above to its stated type."
theorem «the decision and end lemmas have their stated types» :
    (∀ (props : Char → Props) (c : Char) (cs : List Char) (i : Nat) (hi : i < cs.length),
      breaksBefore (scanStateOf (props c) ((cs.take i).map props)) (props cs[i]) = true ↔
        IsBoundary props (c :: cs) (i + 1)) ∧
    (∀ (props : Char → Props) (cs : List Char) (_h : cs ≠ []), IsBoundary props cs 0) ∧
    (∀ (props : Char → Props) (cs : List Char) (_h : cs ≠ []),
      IsBoundary props cs cs.length) :=
  ⟨Segmentation.breaksBefore_iff_isBoundary, Segmentation.isBoundary_zero,
    Segmentation.isBoundary_length⟩
