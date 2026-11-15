import Segmentation

-- Code points no range covers must read as `props` reads them: `gcbOf`, `extPictOf` and
-- `incbOf` fall back to `.other`, `false` and `.none`. A different default would make
-- `propsLookup` disagree with `props` in every gap between ranges.
theorem «propsDefault is Other, not pictographic, InCB None for uncovered code points» :
    Segmentation.Tables.propsDefault =
      ({ gcb := .other, extPict := false, incb := .none } : Segmentation.Props) :=
  rfl
