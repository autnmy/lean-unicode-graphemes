import SegmentationDev.Gate.Axioms
import Segmentation

/-!
Checks of the scan state invariants in `Segmentation.ScanInvariants`: each lemma has the type
the follow-up proofs rely on and uses only the standard axioms, and small hand-built texts give
the flags and boundaries the rules of UAX #29 say. The property values are written by hand, so
no check reads the generated tables.

`IsBoundary` holds functions, so it has no `Decidable` instance; the boundary checks go through
`breaksBefore_iff_isBoundary` and decide `breaksBefore` instead.
-/

namespace SegmentationDev.Test.ScanInvariants

open Segmentation

/-! ## Statements -/

theorem «scanStateOf is the fold of push from start» :
    ∀ (p : Props) (ps : List Props),
      Segmentation.scanStateOf p ps = ps.foldl ScanState.push (ScanState.start p) :=
  fun _ _ => rfl

-- Each conjunct fails to elaborate if a lemma's arguments or statement differ from the stated
-- signature, which later proofs apply as written.
theorem «scan invariants: every flag lemma has its stated type» :
    (∀ (p : Props) (ps : List Props),
      (scanStateOf p ps).prev = (p :: ps).getLast (List.cons_ne_nil p ps)) ∧
    (∀ (p : Props) (ps : List Props),
      (scanStateOf p ps).linkerTail = true ↔
        Left.Holds (.ending (.seq (.one (incbIs .linker)) (.star (incbIs .extend)))) (p :: ps)) ∧
    (∀ (p : Props) (ps : List Props),
      (scanStateOf p ps).pictTail = true ↔
        Left.Holds (.ending (.seq (.one isExtPict) (.star (gcbIn [.extend])))) (p :: ps)) ∧
    (∀ (p : Props) (ps : List Props),
      (scanStateOf p ps).zwjAfterPict = true ↔
        Left.Holds (.ending (.seq (.one isExtPict)
          (.seq (.star (gcbIn [.extend])) (.one (gcbIn [.zwj]))))) (p :: ps)) ∧
    (∀ (p : Props) (ps : List Props),
      (scanStateOf p ps).riOdd = true ↔
        Left.Holds (.sot (.seq (.pairs (gcbIn [.regionalIndicator]))
          (.one (gcbIn [.regionalIndicator])))) (p :: ps) ∨
        Left.Holds (.notThen (gcbIn [.regionalIndicator])
          (.seq (.pairs (gcbIn [.regionalIndicator])) (.one (gcbIn [.regionalIndicator]))))
          (p :: ps)) :=
  ⟨scanStateOf_prev, scanStateOf_linkerTail, scanStateOf_pictTail,
    scanStateOf_zwjAfterPict, scanStateOf_riOdd⟩

theorem «scan invariants: the decision and end lemmas have their stated types» :
    (∀ (props : Char → Props) (c : Char) (cs : List Char) (i : Nat) (hi : i < cs.length),
      breaksBefore (scanStateOf (props c) ((cs.take i).map props)) (props cs[i]) = true ↔
        IsBoundary props (c :: cs) (i + 1)) ∧
    (∀ (props : Char → Props) (cs : List Char) (_h : cs ≠ []), IsBoundary props cs 0) ∧
    (∀ (props : Char → Props) (cs : List Char) (_h : cs ≠ []),
      IsBoundary props cs cs.length) :=
  ⟨breaksBefore_iff_isBoundary, isBoundary_zero, isBoundary_length⟩

-- A proof by `sorry` depends on `sorryAx`, and one by `native_decide` on an axiom that tactic
-- adds, so failing on any axiom outside the three standard ones makes `lake test` fail and name
-- the lemma.
#assert_axioms Segmentation.scanStateOf_prev Segmentation.scanStateOf_linkerTail
  Segmentation.scanStateOf_pictTail Segmentation.scanStateOf_zwjAfterPict
  Segmentation.scanStateOf_riOdd Segmentation.breaksBefore_iff_isBoundary
  Segmentation.isBoundary_zero Segmentation.isBoundary_length

/-! ## Hand-built property values -/

def riProps : Props := { gcb := .regionalIndicator, extPict := false, incb := .none }
def otherProps : Props := { gcb := .other, extPict := false, incb := .none }
def zwjProps : Props := { gcb := .zwj, extPict := false, incb := .none }
def pictProps : Props := { gcb := .other, extPict := true, incb := .none }
def extendProps : Props := { gcb := .extend, extPict := false, incb := .none }
def linkerProps : Props := { gcb := .extend, extPict := false, incb := .linker }
def incbExtendProps : Props := { gcb := .extend, extPict := false, incb := .extend }
def crProps : Props := { gcb := .cr, extPict := false, incb := .none }
def lfProps : Props := { gcb := .lf, extPict := false, incb := .none }

/-- 'z' is a ZWJ and every other character an Extended_Pictographic code point. -/
def zwjPictLookup (c : Char) : Props := if c = 'z' then zwjProps else pictProps

/-- 'r' is a regional indicator and every other character GCB Other. -/
def riLookup (c : Char) : Props := if c = 'r' then riProps else otherProps

/-! ## Flags -/

theorem «scanStateOf: three regional indicators leave riOdd true» :
    (scanStateOf riProps [riProps, riProps]).riOdd = true := by
  decide

theorem «scanStateOf: four regional indicators leave riOdd false» :
    (scanStateOf riProps [riProps, riProps, riProps]).riOdd = false := by
  decide

-- GB13 needs the RI run to follow a non-RI code point, so a ZWJ inside a run starts a new
-- count: RI, ZWJ, RI ends in a run of one (odd), and RI, ZWJ, RI, RI in a run of two (even).
theorem «riOdd restarts its count after a ZWJ between regional indicators» :
    (scanStateOf riProps [zwjProps, riProps]).riOdd = true ∧
    (scanStateOf riProps [zwjProps, riProps, riProps]).riOdd = false := by
  decide

-- A second ZWJ is not GCB Extend, so it ends the run GB11 reads; the two-element case pins
-- that the flag is not simply always false.
theorem «ExtPict ZWJ ZWJ leaves zwjAfterPict false but ExtPict ZWJ sets it» :
    (scanStateOf pictProps [zwjProps, zwjProps]).zwjAfterPict = false ∧
    (scanStateOf pictProps [zwjProps]).zwjAfterPict = true := by
  decide

-- GB11's left side is ExtPict Extend* ZWJ: an Extend run between them keeps it, and a GCB
-- Other code point breaks it.
theorem «zwjAfterPict crosses an Extend run but not an Other code point» :
    (scanStateOf pictProps [extendProps, extendProps, zwjProps]).zwjAfterPict = true ∧
    (scanStateOf pictProps [otherProps, zwjProps]).zwjAfterPict = false := by
  decide

-- GB9c's left side is InCB Linker then InCB Extend*: InCB Extend keeps the flag, and an InCB
-- None code point clears it, even when an InCB Extend follows.
theorem «Linker then InCB None leaves linkerTail false but Linker Extend keeps it» :
    (scanStateOf linkerProps [otherProps]).linkerTail = false ∧
    (scanStateOf linkerProps [incbExtendProps]).linkerTail = true ∧
    (scanStateOf linkerProps [incbExtendProps, incbExtendProps]).linkerTail = true ∧
    (scanStateOf linkerProps [incbExtendProps, otherProps, incbExtendProps]).linkerTail = false := by
  decide

/-! ## Boundaries -/

theorem «ExtPict ZWJ ExtPict has no boundary at position 2 through GB11» :
    breaksBefore (scanStateOf (zwjPictLookup 'p') [zwjPictLookup 'z'])
        (zwjPictLookup 'q') = false ∧
      ¬ IsBoundary zwjPictLookup ['p', 'z', 'q'] 2 := by
  refine ⟨by decide, fun h => ?_⟩
  have hb := (breaksBefore_iff_isBoundary zwjPictLookup 'p' ['z', 'q'] 1 (by decide)).mpr h
  exact absurd hb (by decide)

-- In ExtPict, ZWJ, ZWJ, ExtPict the text before the pictograph does not end with ExtPict
-- Extend* ZWJ, so GB11 fails and GB999 breaks at position 3.
theorem «GB11 does not join a pictograph after ZWJ ZWJ» :
    IsBoundary zwjPictLookup ['p', 'z', 'z', 'p'] 3 :=
  (breaksBefore_iff_isBoundary zwjPictLookup 'p' ['z', 'z', 'p'] 2 (by decide)).mp (by decide)

theorem «CR then LF has no boundary at position 1» :
    ¬ IsBoundary (fun c => if c = '\r' then crProps else lfProps) ['\r', '\n'] 1 := by
  intro h
  have hb := (breaksBefore_iff_isBoundary (fun c => if c = '\r' then crProps else lfProps)
    '\r' ['\n'] 0 (by decide)).mpr h
  exact absurd hb (by decide)

-- The first rule that applies decides: after CR, GB4 (break) comes before GB9 (no break
-- before Extend), so CR then Extend has a boundary at position 1.
theorem «GB4 break after CR wins over the later GB9 no-break before Extend» :
    IsBoundary (fun c => if c = '\r' then crProps else incbExtendProps) ['\r', 'e'] 1 :=
  (breaksBefore_iff_isBoundary (fun c => if c = '\r' then crProps else incbExtendProps)
    '\r' ['e'] 0 (by decide)).mp (by decide)

-- With nothing before the first RI, only GB12 (start of text, an odd run of RI) can join the
-- pair; GB13 needs a non-RI code point before the run.
theorem «two RI at the start of the text have no boundary at position 1 through GB12» :
    ¬ IsBoundary riLookup ['r', 'r'] 1 := by
  intro h
  have hb := (breaksBefore_iff_isBoundary riLookup 'r' ['r'] 0 (by decide)).mpr h
  exact absurd hb (by decide)

theorem «RI after a non-RI followed by an RI has no boundary through GB13» :
    ¬ IsBoundary riLookup ['a', 'r', 'r'] 2 := by
  intro h
  have hb := (breaksBefore_iff_isBoundary riLookup 'a' ['r', 'r'] 1 (by decide)).mpr h
  exact absurd hb (by decide)

-- Before the third RI of RI, RI, RI the run has even length, so neither GB12 nor GB13 applies
-- and GB999 breaks at position 2.
theorem «a third regional indicator after an even pair starts a new cluster» :
    IsBoundary riLookup ['r', 'r', 'r'] 2 :=
  (breaksBefore_iff_isBoundary riLookup 'r' ['r', 'r'] 1 (by decide)).mp (by decide)

theorem «two Other code points have a boundary at position 1 through GB999» :
    IsBoundary (fun _ => otherProps) ['a', 'b'] 1 :=
  (breaksBefore_iff_isBoundary (fun _ => otherProps) 'a' ['b'] 0 (by decide)).mp (by decide)

end SegmentationDev.Test.ScanInvariants
