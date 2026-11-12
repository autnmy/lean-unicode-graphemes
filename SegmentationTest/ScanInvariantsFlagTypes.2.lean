import Segmentation

open Segmentation

-- "Ascribe every lemma above to its stated type."
theorem «the five flag lemmas have their stated types» :
    (∀ (p : Props) (ps : List Props),
      (scanStateOf p ps).prev = (p :: ps).getLast (List.cons_ne_nil p ps)) ∧
    (∀ (p : Props) (ps : List Props),
      (scanStateOf p ps).linkerTail = true ↔
        Left.Holds (.ending (.seq (.one (incbIs .Linker)) (.star (incbIs .Extend)))) (p :: ps)) ∧
    (∀ (p : Props) (ps : List Props),
      (scanStateOf p ps).pictTail = true ↔
        Left.Holds (.ending (.seq (.one isExtPict) (.star (gcbIn [.Extend])))) (p :: ps)) ∧
    (∀ (p : Props) (ps : List Props),
      (scanStateOf p ps).zwjAfterPict = true ↔
        Left.Holds (.ending (.seq (.one isExtPict)
          (.seq (.star (gcbIn [.Extend])) (.one (gcbIn [.ZWJ]))))) (p :: ps)) ∧
    (∀ (p : Props) (ps : List Props),
      (scanStateOf p ps).riOdd = true ↔
        Left.Holds (.sot (.seq (.pairs (gcbIn [.RI])) (.one (gcbIn [.RI])))) (p :: ps) ∨
        Left.Holds (.notThen (gcbIn [.RI])
          (.seq (.pairs (gcbIn [.RI])) (.one (gcbIn [.RI])))) (p :: ps)) :=
  ⟨Segmentation.scanStateOf_prev, Segmentation.scanStateOf_linkerTail,
    Segmentation.scanStateOf_pictTail, Segmentation.scanStateOf_zwjAfterPict,
    Segmentation.scanStateOf_riOdd⟩
