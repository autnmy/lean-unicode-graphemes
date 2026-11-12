import Segmentation

set_option maxRecDepth 20000 in
theorem «props gives the file defaults for an unlisted code point and for U+10FFFF» :
    (Segmentation.Tables.props (Char.ofNat 0x10FFFF) ==
        { gcb := Segmentation.GCB.Other, extPict := false, incb := Segmentation.InCB.None } &&
     Segmentation.Tables.props 'A' ==
        { gcb := Segmentation.GCB.Other, extPict := false, incb := Segmentation.InCB.None }) = true := by
  decide
