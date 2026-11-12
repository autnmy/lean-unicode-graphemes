import Segmentation
import TableGen

-- A check, run by `lake test`, that for every code point from U+0000 to U+10FFFF the lookup equals the value the UCD files give.
-- The generator and the reference share this parser, so a name it does not know must be an
-- error: read as the default `Other`, both sides would agree and the exhaustive check would pass.
theorem «R5 parseGcb rejects a misspelled value name instead of falling back to Other» :
    (match TableGen.parseGcb "1F1E6..1F1FF  ; Regional_Indicatr # So  [26] REGIONAL INDICATOR SYMBOL LETTER A..Z\n" with
     | .error _ => true
     | .ok _ => false) = true := by decide
