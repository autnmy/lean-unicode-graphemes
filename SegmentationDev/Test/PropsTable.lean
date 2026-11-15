import SegmentationDev.Gate.Axioms
import Segmentation

/-!
# The combined property table agrees with the three lookups

`Segmentation.Tables.propsLookup` reads all three properties of a code point with one binary
search in `propsRanges`. These checks pin the theorem that makes it equal to `props`, pin that
it really is one lookup, and sample it on code points that each exercise a different table and
both ends of the code point space.
-/

-- "`Segmentation.Tables.propsLookup c = Segmentation.Tables.props c` is proved for every `Char c`
-- by `Tables.propsLookup_eq_props`, not sampled."
-- The ascription fails to elaborate if the theorem is renamed, takes a hypothesis, or is restated.
theorem «propsLookup_eq_props has the unconditional statement for every Char» : True := by
  have _x : ∀ c : Char, Segmentation.Tables.propsLookup c = Segmentation.Tables.props c :=
    Segmentation.Tables.propsLookup_eq_props
  trivial

-- A definition of `propsLookup` that called `props`, or the three source tables, would make the
-- theorem above hold without giving the single lookup the fast segmenter needs; this fails then.
theorem «propsLookup is a single Range.lookup in propsRanges» : True := by
  have _x : ∀ c : Char, Segmentation.Tables.propsLookup c =
      Segmentation.Tables.Range.lookup Segmentation.Tables.propsDefault
        Segmentation.Tables.propsRanges c.toNat :=
    fun _ => rfl
  trivial

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

#assert_axioms Segmentation.Tables.propsLookup_eq_props
