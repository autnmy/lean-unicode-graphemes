import Segmentation
import TableGen

-- A generator, `lake exe gen-tables`, that writes Lean range tables for `Grapheme_Cluster_Break`, `Extended_Pictographic` and `Indic_Conjunct_Break`, each generated file starting with the Unicode licence notice.
-- U+0043 is claimed by two ranges with different values. Keeping either one silently would
-- write a table that no longer says what the file says.
theorem «R2 normalize rejects overlapping entries with different values instead of keeping the last» :
    (match TableGen.normalize
        [({ lo := 0x41, hi := 0x45, value := Segmentation.GCB.Control } : Segmentation.Tables.Range Segmentation.GCB),
         { lo := 0x43, hi := 0x43, value := Segmentation.GCB.Extend }] with
     | .error _ => true
     | .ok _ => false) = true := by decide
