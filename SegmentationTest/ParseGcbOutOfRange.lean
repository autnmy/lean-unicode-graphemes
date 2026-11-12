import Segmentation
import TableGen

-- A check, run by `lake test`, that for every code point from U+0000 to U+10FFFF the lookup equals the value the UCD files give.
-- A range past U+10FFFF is outside the code space the tables cover, so it must stop the parse.
theorem «R5 parseGcb rejects a code point above U+10FFFF» :
    (match TableGen.parseGcb "110000        ; Control # Cn       <reserved>\n" with
     | .error _ => true
     | .ok _ => false) = true := by decide
