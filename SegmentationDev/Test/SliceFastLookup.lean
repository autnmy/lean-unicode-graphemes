import Lean
import Segmentation
import SegmentationDev.Gate.Axioms

/-!
# The scanner's block-indexed property lookup

`Segmentation.nonAsciiProps` searches only the ranges of `Tables.propsRanges` that
`propsBlockStarts` gives for a code point's block. `nonAsciiProps_eq_propsLookup` proves it equal
to `Tables.propsLookup` for every character, whatever the index holds, because each window is
checked by `Tables.Range.windowHolds` before it is searched. The checks here pin that statement,
compare both lookups on the edges of the Hangul syllable block, and check that the index gives a
passing window for every block, so the scanner does not quietly fall back to the whole-table
search.
-/

-- "the equality theorem is stated for every `Char`"
theorem nonAsciiProps_eq_propsLookup_type_is_for_every_char : True := by
  have _x : ∀ c : Char, Segmentation.nonAsciiProps c = Segmentation.Tables.propsLookup c :=
    Segmentation.nonAsciiProps_eq_propsLookup
  trivial

-- "code points U+ABFF, U+AC00, U+AC01, U+AC1C, U+D7A3 and U+D7A4 give the same props as
-- `Tables.propsLookup`". U+AC00 and U+AC1C are LV syllables, U+AC01 and U+D7A3 are LVT, and
-- U+ABFF and U+D7A4 are just outside the syllable block.
#guard [0xABFF, 0xAC00, 0xAC01, 0xAC1C, 0xD7A3, 0xD7A4].all fun n =>
  Segmentation.nonAsciiProps (Char.ofNat n) == Segmentation.Tables.propsLookup (Char.ofNat n)

-- The Hangul answers are not the defaults, so the equality above cannot pass only because both
-- lookups fell back to them.
#guard (Segmentation.nonAsciiProps (Char.ofNat 0xAC00)).gcb == Segmentation.GCB.lv
#guard (Segmentation.nonAsciiProps (Char.ofNat 0xD7A3)).gcb == Segmentation.GCB.lvt

-- Code points of every other kind the benchmark's large input holds, and both ends of the
-- non-ASCII code space, including one past the last block of the index.
#guard [0x0080, 0x0301, 0x0915, 0x094D, 0x1100, 0x1161, 0x11AB, 0x200D, 0x4E2D, 0x1F1E6,
    0x1F3FE, 0x1F468, 0x1F600, 0xE0100, 0xE01EF, 0xE01F0, 0x10FFFF].all fun n =>
  Segmentation.nonAsciiProps (Char.ofNat n) == Segmentation.Tables.propsLookup (Char.ofNat n)

-- Every block of the index, at its first and its last code point, gets a window from
-- `propsBlockWindow`, the function `nonAsciiProps` reads, so the scanner takes the short search
-- on every code point the index covers rather than falling back to the whole table.
#guard (List.range (Segmentation.propsBlockStarts.size - 1)).all fun block =>
  (Segmentation.propsBlockWindow (block * Segmentation.propsBlockSize)).isSome &&
    (Segmentation.propsBlockWindow ((block + 1) * Segmentation.propsBlockSize - 1)).isSome

-- The index covers the code point the last range ends at.
#guard (Segmentation.propsBlockWindow
  ((Segmentation.Tables.propsRanges.back?.map (·.hi)).getD 0)).isSome

-- The scan reads non-ASCII properties through `nonAsciiProps`. `scanClusters` is defined by
-- well-founded recursion, so its body sits in auxiliary definitions; the walk follows every
-- `Segmentation` definition it reaches.
open Lean in
theorem scan_clusters_reads_non_ascii_props_through_block_index : True := by
  run_tac do
    let env ← getEnv
    let mut seen : NameSet := {}
    let mut todo := #[``Segmentation.scanClusters]
    let mut i := 0
    while i < todo.size do
      let n := todo[i]!
      i := i + 1
      if seen.contains n then continue
      seen := seen.insert n
      if n != ``Segmentation.nonAsciiProps && (`Segmentation).isPrefixOf n then
        if let some (.defnInfo info) := env.find? n then
          for c in info.value.getUsedConstants do
            todo := todo.push c
    unless seen.contains ``Segmentation.nonAsciiProps do
      throwError "scanClusters does not look up non-ASCII code points with nonAsciiProps"
  trivial

-- "`#assert_axioms` on the theorem passes with only `propext`, `Classical.choice`, `Quot.sound`".
#assert_axioms Segmentation.nonAsciiProps_eq_propsLookup
  Segmentation.Tables.Range.lookup_search_window_eq_lookup Segmentation.nonAsciiProps
  Segmentation.propsBlockStarts Segmentation.Tables.Range.windowHolds
  Segmentation.propsBlockWindow Segmentation.propsBlockWindow_windowHolds
  Segmentation.searchPropsWindow Segmentation.searchPropsWindow_eq_propsLookup
