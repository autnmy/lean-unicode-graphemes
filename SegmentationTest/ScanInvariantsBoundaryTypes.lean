import Segmentation.ScanInvariants

open Segmentation

-- "Ascribe every lemma above to its stated type."
theorem «scan invariants: the decision and end lemmas have their stated types» :
    (∀ (props : Char → Props) (c : Char) (cs : List Char) (i : Nat) (hi : i < cs.length),
      breaksBefore (scanStateOf (props c) ((cs.take i).map props)) (props cs[i]) = true ↔
        IsBoundary props (c :: cs) (i + 1)) ∧
    (∀ (props : Char → Props) (cs : List Char) (_h : cs ≠ []), IsBoundary props cs 0) ∧
    (∀ (props : Char → Props) (cs : List Char) (_h : cs ≠ []),
      IsBoundary props cs cs.length) :=
  ⟨breaksBefore_iff_isBoundary, isBoundary_zero, isBoundary_length⟩
