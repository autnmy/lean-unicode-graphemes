import Segmentation

open Segmentation in
-- Expected values are written by hand from auxiliary/GraphemeBreakProperty.txt,
-- so a wrong name mapping shared by the generator and the parser still fails here.
-- "The tables are data, not a theorem: the UCD files are the definition."
set_option maxRecDepth 20000 in
theorem «props gives the Grapheme_Cluster_Break value the UCD file lists for one code point of every value» :
    (['\u000D', '\u000A', '\u0000', '\u0300', '\u200D', Char.ofNat 0x1F1E6, '\u0600',
      '\u0903', '\u1100', '\u1160', '\u11A8', '\uAC00', '\uAC01', 'A'].map
        fun c => (Segmentation.Tables.props c).gcb)
      = [GCB.cr, GCB.lf, GCB.control, GCB.extend, GCB.zwj, GCB.regionalIndicator, GCB.prepend,
         GCB.spacingMark, GCB.l, GCB.v, GCB.t, GCB.lv, GCB.lvt, GCB.other] := by
  decide
