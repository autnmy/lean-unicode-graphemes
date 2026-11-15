import Segmentation

-- "merging the three sorted range lists into one sorted list of ranges, each carrying a whole
-- `Props`." The binary search in `Range.lookup` is only right on a sorted table.
open Segmentation.Tables in
set_option maxRecDepth 20000 in
theorem «propsRanges is sorted with no overlapping ranges» : Range.Sorted propsRanges := by
  decide
