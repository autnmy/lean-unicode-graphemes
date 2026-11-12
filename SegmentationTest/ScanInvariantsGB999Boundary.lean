import Segmentation

open Segmentation

def scanInvGB999Props (_ : Char) : Props := { gcb := .Other, extPict := false, incb := .None }

-- "GB999 (index 15) always applies inside the text and matches the fallback. Both directions of the `↔` must hold."
theorem «two Other code points have a boundary at position 1 through GB999» :
    IsBoundary scanInvGB999Props ['a', 'b'] 1 :=
  (breaksBefore_iff_isBoundary scanInvGB999Props 'a' ['b'] 0 (by decide)).mp (by decide)
