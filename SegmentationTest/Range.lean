import Segmentation.Tables.Range

/-!
# Range lookup checks

Compile-time checks of `Segmentation.Tables.Range.lookup` on a table with a gap
between two ranges. The test driver imports this module, so a failed `#guard`
stops `lake test`.
-/

namespace SegmentationTest.RangeChecks

open Segmentation.Tables

/-- Two ranges with a gap between them: `A`..`Z` carry 1, `a`..`z` carry 2. -/
def twoRangeTable : Array (Range Nat) :=
  #[{ lo := 0x41, hi := 0x5A, value := 1 }, { lo := 0x61, hi := 0x7A, value := 2 }]

#guard Range.lookup 0 twoRangeTable 0x40 == 0
#guard Range.lookup 0 twoRangeTable 0x41 == 1
#guard Range.lookup 0 twoRangeTable 0x5A == 1
#guard Range.lookup 0 twoRangeTable 0x5B == 0
#guard Range.lookup 0 twoRangeTable 0x60 == 0
#guard Range.lookup 0 twoRangeTable 0x61 == 2
#guard Range.lookup 0 twoRangeTable 0x7A == 2
#guard Range.lookup 0 twoRangeTable 0x10FFFF == 0

end SegmentationTest.RangeChecks
