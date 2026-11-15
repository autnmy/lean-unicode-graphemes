import Lean
import SegmentationDev.Gate.Axioms
import Segmentation

/-!
# The combined property table agrees with the three lookups

`Segmentation.Tables.propsLookup` reads all three properties of a code point with one binary
search in `propsRanges`. These checks pin the theorem that makes it equal to `props`, pin that
it really is one lookup in a table built once, check the general merge lemmas and small merges
by hand-picked boundaries, and sample the lookup on code points that each exercise a different
table and both ends of the code point space.
-/

/-! ### The theorem and the shape of `propsLookup` -/

-- "`Segmentation.Tables.propsLookup c = Segmentation.Tables.props c` is proved for every `Char c`
-- by `Tables.propsLookup_eq_props`, not sampled."
-- The ascription fails to elaborate if the theorem is renamed, takes a hypothesis, or is restated.
theorem «propsLookup_eq_props has the unconditional statement for every Char» : True := by
  have _x : ∀ c : Char, Segmentation.Tables.propsLookup c = Segmentation.Tables.props c :=
    Segmentation.Tables.propsLookup_eq_props
  trivial

-- "Define `Segmentation.Tables.propsLookup (c : Char) : Segmentation.Props` as one lookup in it."
-- Holding by `rfl` pins the definition to a single binary search over the combined table, so a
-- definition that calls `props` or the three source tables fails here.
open Segmentation.Tables in
theorem «propsLookup_is_one_lookup_in_propsRanges» :
    ∀ c : Char, propsLookup c = Range.lookup propsDefault propsRanges c.toNat :=
  fun _ => rfl

open Segmentation in
-- A code point no table covers must read the same defaults `props` uses: `.other`, `false`,
-- `.none`.
theorem «propsDefault_is_other_not_pictographic_incb_none» :
    Segmentation.Tables.propsDefault = { gcb := GCB.other, extPict := false, incb := InCB.none } :=
  rfl

-- "Compiled code builds the table once as a closed term."
-- A top-level constant with no parameters is evaluated once when compiled code starts. If the
-- table took an argument, or `propsLookup` merged the source tables in its own body instead of
-- naming `propsRanges`, the merge would run again on every call.
open Lean in
theorem «propsRanges is a closed constant that propsLookup reads instead of rebuilding the table per call» :
    True := by
  run_tac do
    let env ← getEnv
    match env.find? ``Segmentation.Tables.propsRanges with
    | some (.defnInfo info) =>
      if info.type.isForall then
        throwError m!"propsRanges takes arguments, so it is not a closed term: {info.type}"
    | _ => throwError "propsRanges is not a definition"
    match env.find? ``Segmentation.Tables.propsLookup with
    | some (.defnInfo info) =>
      let consts := info.value.getUsedConstants
      unless consts.contains ``Segmentation.Tables.propsRanges do
        throwError "propsLookup does not read the closed table propsRanges"
      if consts.contains ``Segmentation.Tables.Range.mergeWith then
        throwError "propsLookup merges the tables on every call"
    | _ => throwError "propsLookup is not a definition"
  trivial

-- "The proof uses no axiom beyond `propext`, `Classical.choice` and `Quot.sound`, and no
-- `sorry`, `native_decide`, `implemented_by`, `extern` or `partial` (CI's forbidden-words scan
-- rejects most of these)."
-- A proof by `sorry` leaves `sorryAx` and one by compiler evaluation leaves `Lean.ofReduceBool`
-- among the theorem's axioms. A `partial` definition is stored as an opaque constant, and a
-- compiler substitute is recorded as an attribute, so neither shows up as an axiom: the
-- definitions the theorem is about are checked for both directly. The keyword scan does not
-- look for `partial` at all, so this is the only automated check of it.
open Lean in
theorem «propsLookup_eq_props rests on no sorry, compiler-evaluated proof, compiler substitute or partial definition» :
    True := by
  run_tac do
    let used ← collectAxioms ``Segmentation.Tables.propsLookup_eq_props
    let bad := SegmentationDev.Gate.disallowedAxioms used
    unless bad.isEmpty do
      throwError m!"propsLookup_eq_props uses disallowed axioms {bad}"
    let env ← getEnv
    for name in [``Segmentation.Tables.propsLookup, ``Segmentation.Tables.propsRanges,
        ``Segmentation.Tables.Range.mergeWith] do
      match env.find? name with
      | some (.defnInfo _) => pure ()
      | some _ => throwError m!"{name} is not a plain definition (a partial definition is opaque)"
      | none => throwError m!"{name} is missing"
      if (Compiler.getImplementedBy? env name).isSome then
        throwError m!"{name} has a compiled substitute the proof does not cover"
      if isExtern env name then
        throwError m!"{name} is bound to foreign code the proof does not cover"
  trivial

/-! ### The general merge lemmas -/

-- "A kernel check over every code point is too slow, so prove it through a general lemma about
-- merging sorted range lists plus the existing facts in `Segmentation/RangeLookup.lean`
-- (`Range.lookup_eq_scan`, `Range.Sorted`) and `Segmentation/TableLookup.lean` (`*_sorted`,
-- `props_eq_scan`)."
-- The statement quantifies over every value type and every pair of sorted lists, so a lemma
-- proved only for the three concrete tables does not satisfy it.
theorem «mergeWith keeps any two sorted range lists sorted» :
    ∀ {α β γ : Type} (f : α → β → γ) (da : α) (db : β)
      (a : List (Segmentation.Tables.Range α)) (b : List (Segmentation.Tables.Range β)),
      Segmentation.Tables.Range.chainOK a = true →
      Segmentation.Tables.Range.chainOK b = true →
      Segmentation.Tables.Range.chainOK (Segmentation.Tables.Range.mergeWith f da db a b) = true := by
  intro α β γ f da db a b ha hb
  apply Segmentation.Tables.Range.chainOK_mergeWith <;> assumption

-- The statement holds for every code point `n` and every pair of sorted lists of any value
-- types, so it covers overlaps, gaps and shared endpoints without sampling them.
theorem «mergeWith scans as the pair of scans for any two sorted range lists» :
    ∀ {α β γ : Type} (f : α → β → γ) (da : α) (db : β)
      (a : List (Segmentation.Tables.Range α)) (b : List (Segmentation.Tables.Range β)) (n : Nat),
      Segmentation.Tables.Range.chainOK a = true →
      Segmentation.Tables.Range.chainOK b = true →
      Segmentation.Tables.Range.scanList (f da db) (Segmentation.Tables.Range.mergeWith f da db a b) n =
        f (Segmentation.Tables.Range.scanList da a n) (Segmentation.Tables.Range.scanList db b n) := by
  intro α β γ f da db a b n ha hb
  apply Segmentation.Tables.Range.scanList_mergeWith <;> assumption

/-! ### Small merges, read at their boundaries -/

-- "Compute the combined table in Lean by merging the three sorted range lists into one sorted
-- list of ranges, each carrying a whole `Props`."
-- The binary search is only right on a sorted table, so a merge that emits an empty range
-- (lo > hi) or two overlapping pieces at a shared endpoint must fail here.
open Segmentation.Tables in
set_option maxRecDepth 20000 in
theorem «mergeWith output of overlapping and touching ranges is still sorted» :
    (Range.chainOK
      (Range.mergeWith (fun (x : Nat) (y : Bool) => (x, y)) 0 false
        [({ lo := 0, hi := 10, value := 1 } : Range Nat), { lo := 20, hi := 30, value := 2 }]
        [({ lo := 5, hi := 20, value := true } : Range Bool), { lo := 31, hi := 40, value := true }])) =
      true := by
  decide

-- The same lists: they overlap (5..10), share an endpoint (20 ends one range and starts the
-- other), touch across lists (30 then 31), and leave gaps (11..19 in the first list, past 40 in
-- both). Each point read is one side of a cut, where an off-by-one (hi against lo - 1) shows up.
open Segmentation.Tables in
set_option maxRecDepth 20000 in
theorem «mergeWith keeps both values on each side of every split point» :
    ([0, 4, 5, 10, 11, 19, 20, 21, 30, 31, 40, 41].map
      (Range.scanList ((0 : Nat), false)
        (Range.mergeWith (fun (x : Nat) (y : Bool) => (x, y)) 0 false
          [({ lo := 0, hi := 10, value := 1 } : Range Nat), { lo := 20, hi := 30, value := 2 }]
          [({ lo := 5, hi := 20, value := true } : Range Bool), { lo := 31, hi := 40, value := true }]))) =
      [(1, false), (1, false), (1, true), (1, true), (0, true), (0, true), (2, true), (2, false),
        (2, false), (0, true), (0, true), (0, false)] := by
  decide

-- When both lists hold the same range, the merge must emit it once with both values, and must
-- not leave an empty piece that hides the code points next to it.
open Segmentation.Tables in
set_option maxRecDepth 20000 in
theorem «mergeWith handles two ranges with the same lo and hi» :
    ([2, 3, 7, 8].map
      (Range.scanList ((0 : Nat), false)
        (Range.mergeWith (fun (x : Nat) (y : Bool) => (x, y)) 0 false
          [({ lo := 3, hi := 7, value := 5 } : Range Nat)]
          [({ lo := 3, hi := 7, value := true } : Range Bool)]))) =
      [(0, false), (5, true), (5, true), (0, false)] := by
  decide

open Segmentation.Tables in
-- The inputs overlap (3..8 against 5..12), touch (13 right after 12) and leave gaps (0..2,
-- 15..19, above 22), so a wrong split point shows up as an unsorted result or a wrong value.
theorem «mergeWith_of_sorted_overlapping_lists_is_sorted_and_reads_both_values» :
    (let a : List (Range Nat) := [{ lo := 3, hi := 8, value := 1 }, { lo := 20, hi := 22, value := 2 }]
     let b : List (Range Bool) := [{ lo := 5, hi := 12, value := true }, { lo := 13, hi := 14, value := true }]
     let merged := Range.mergeWith Prod.mk 0 false a b
     Range.chainOK merged &&
       ([0, 2, 3, 4, 5, 8, 9, 12, 13, 14, 15, 19, 20, 22, 23].map
          (fun n => Range.scanList (0, false) merged n)) ==
         [(0, false), (0, false), (1, false), (1, false), (1, true), (1, true), (0, true),
          (0, true), (0, true), (0, true), (0, false), (0, false), (2, false), (2, false),
          (0, false)]) = true := by
  decide

-- Overlap (0..10 with 5..15), a gap no range covers (16..19), and ranges that touch across the
-- two lists (20..25 then 26..30). Each probe sits on or next to a boundary, where a split written
-- as `hi` instead of `lo - 1` would give the wrong pair for exactly one code point.
open Segmentation.Tables in
theorem «mergeWith_splits_overlapping_touching_and_gap_ranges» :
    let a : List (Range Nat) :=
      [{ lo := 0, hi := 10, value := 1 }, { lo := 20, hi := 25, value := 2 }]
    let b : List (Range Bool) :=
      [{ lo := 5, hi := 15, value := true }, { lo := 26, hi := 30, value := true }]
    let merged := Range.mergeWith Prod.mk 0 false a b
    Range.chainOK merged = true ∧
    ([0, 4, 5, 10, 11, 15, 16, 19, 20, 25, 26, 30, 31].map (Range.scanList (0, false) merged)) =
      [(1, false), (1, false), (1, true), (1, true), (0, true), (0, true), (0, false),
       (0, false), (2, false), (2, false), (0, true), (0, true), (0, false)] := by
  decide

-- The first list has a gap at 5..7; the second overlaps both of its ranges, shares the end 12
-- with the first list, and has two ranges that touch at 12 and 13. Every point from 0 to 19 must
-- scan in the merged list as the pair of the two lists' own scans, and the merged list must stay
-- sorted with no empty or overlapping range.
open Segmentation.Tables in
theorem «mergeWith scans as the pair of scans across overlaps, gaps and touching ranges» :
    (let a : List (Range Nat) :=
        [{ lo := 0, hi := 4, value := 1 }, { lo := 8, hi := 12, value := 2 }]
     let b : List (Range Nat) :=
        [{ lo := 3, hi := 9, value := 5 }, { lo := 12, hi := 12, value := 6 },
         { lo := 13, hi := 15, value := 7 }]
     let merged := Range.mergeWith Prod.mk 0 0 a b
     Range.chainOK merged &&
       (List.range 20).all (fun n =>
         Range.scanList (0, 0) merged n == (Range.scanList 0 a n, Range.scanList 0 b n))) = true := by
  decide

/-! ### The combined table itself -/

-- "merging the three sorted range lists into one sorted list of ranges, each carrying a whole
-- `Props`." The binary search in `Range.lookup` is only right on a sorted table; this checks the
-- computed table in the kernel, apart from the general proof in the library.
open Segmentation.Tables in
set_option maxRecDepth 20000 in
theorem «propsRanges is sorted with no overlapping ranges» : Range.Sorted propsRanges := by
  decide

-- "`#guard` checks that `propsLookup` equals `Tables.props` on U+0000, U+0301 (Extend), U+200D
-- (ZWJ), U+094D (InCB Linker), U+0915 (InCB Consonant), U+1F1E6 (Regional Indicator), U+1F600
-- (Extended_Pictographic) and U+10FFFF". Each side is computed independently: `props` runs the
-- three original lookups.
#guard [0x0000, 0x0301, 0x200D, 0x094D, 0x0915, 0x1F1E6, 0x1F600, 0x10FFFF].all fun n =>
  Segmentation.Tables.propsLookup (Char.ofNat n) == Segmentation.Tables.props (Char.ofNat n)

-- The named properties are not the defaults, so the equality above cannot pass only because both
-- sides fell back to `.other`, `false` and `.none`.
#guard (Segmentation.Tables.propsLookup (Char.ofNat 0x0301)).gcb == Segmentation.GCB.extend
#guard (Segmentation.Tables.propsLookup (Char.ofNat 0x200D)).gcb == Segmentation.GCB.zwj
#guard (Segmentation.Tables.propsLookup (Char.ofNat 0x094D)).incb == Segmentation.InCB.linker
#guard (Segmentation.Tables.propsLookup (Char.ofNat 0x0915)).incb == Segmentation.InCB.consonant
#guard (Segmentation.Tables.propsLookup (Char.ofNat 0x1F1E6)).gcb ==
  Segmentation.GCB.regionalIndicator
#guard (Segmentation.Tables.propsLookup (Char.ofNat 0x1F600)).extPict == true

-- The same equality, evaluated by the kernel rather than by compiled code.
set_option maxRecDepth 20000 in
theorem «propsLookup_equals_props_on_listed_code_points» :
    ([0x0000, 0x0301, 0x200D, 0x094D, 0x0915, 0x1F1E6, 0x1F600, 0x10FFFF].all fun n =>
      decide (Segmentation.Tables.propsLookup (Char.ofNat n) =
        Segmentation.Tables.props (Char.ofNat n))) = true := by
  decide

open Segmentation in
-- The named properties, evaluated by the kernel, plus both ends of the code point space: U+0000
-- is Control and U+10FFFF has only the defaults.
set_option maxRecDepth 20000 in
theorem «propsLookup_reads_named_properties_of_listed_code_points» :
    (Segmentation.Tables.propsLookup (Char.ofNat 0x0301)).gcb = GCB.extend ∧
    (Segmentation.Tables.propsLookup (Char.ofNat 0x200D)).gcb = GCB.zwj ∧
    (Segmentation.Tables.propsLookup (Char.ofNat 0x094D)).incb = InCB.linker ∧
    (Segmentation.Tables.propsLookup (Char.ofNat 0x0915)).incb = InCB.consonant ∧
    (Segmentation.Tables.propsLookup (Char.ofNat 0x1F1E6)).gcb = GCB.regionalIndicator ∧
    (Segmentation.Tables.propsLookup (Char.ofNat 0x1F600)).extPict = true ∧
    Segmentation.Tables.propsLookup (Char.ofNat 0x10FFFF) =
      { gcb := GCB.other, extPict := false, incb := InCB.none } ∧
    (Segmentation.Tables.propsLookup (Char.ofNat 0x0000)).gcb = GCB.control := by
  decide

#assert_axioms Segmentation.Tables.propsLookup_eq_props
