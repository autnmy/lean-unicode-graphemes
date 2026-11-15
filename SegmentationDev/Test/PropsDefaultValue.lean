import Segmentation

open Segmentation in
-- A code point no table covers must read the same defaults `props` uses: `.other`, `false`,
-- `.none`.
theorem «propsDefault_is_other_not_pictographic_incb_none» :
    Segmentation.Tables.propsDefault = { gcb := GCB.other, extPict := false, incb := InCB.none } :=
  rfl
