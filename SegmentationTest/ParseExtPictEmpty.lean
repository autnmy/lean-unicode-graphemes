import Segmentation
import TableGen

-- A check, run by `lake test`, that for every code point from U+0000 to U+10FFFF the lookup equals the value the UCD files give.
-- An empty or truncated file would make every code point read `false` on both the generator and
-- the reference side, so an empty parse result must be an error.
theorem «R5 parseExtPict fails on a file with no Extended_Pictographic entries» :
    (match TableGen.parseExtPict "# emoji-data.txt\n\n0023          ; Emoji                # E0.0   [1] (#\uFE0F)       hash sign\n" with
     | .error _ => true
     | .ok _ => false) = true := by decide
