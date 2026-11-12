import Segmentation.ScanInvariants

open Segmentation

-- "Ascribe every lemma above to its stated type." Each conjunct fails to elaborate if a
-- lemma's arguments or statement differ from the issue's signature.
theorem «scan invariants: every flag lemma has its stated type» :
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
  ⟨scanStateOf_prev, scanStateOf_linkerTail, scanStateOf_pictTail,
    scanStateOf_zwjAfterPict, scanStateOf_riOdd⟩
