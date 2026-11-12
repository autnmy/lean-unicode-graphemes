import Segmentation.ScanInvariants

-- "The merged row 11 splits into GB12 (index 13) and GB13 (index 14)."
-- With nothing before the first RI, only GB12 (start of text, an odd run of RI) can join the
-- pair; GB13 needs a non-RI code point before the run.
open Segmentation in
theorem «two RI at the start of the text have no boundary at position 1 through GB12» :
    ¬ IsBoundary
      (fun _ => ({ gcb := GCB.RI, extPict := false, incb := InCB.None } : Props))
      ['a', 'a'] 1 := by
  intro h
  have hb := (breaksBefore_iff_isBoundary
    (fun _ => ({ gcb := GCB.RI, extPict := false, incb := InCB.None } : Props))
    'a' ['a'] 0 (by decide)).mpr h
  exact absurd hb (by decide)
