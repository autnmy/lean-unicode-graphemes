import Segmentation
import TableGen

-- A check, run by `lake test`, that for every code point from U+0000 to U+10FFFF the lookup equals the value the UCD files give.
-- DerivedCoreProperties.txt mixes many properties. A parser that read the wrong field would take
-- another property's lines as InCB, or lose the three-field InCB line.
-- `decide` decodes the string literal while elaborating, one nested step per
-- character, which needs more than the default recursion depth.
set_option maxRecDepth 20000 in
theorem «R5 parseIncb reads only InCB lines and takes the value from the third field» :
    (match TableGen.parseIncb
        "0915          ; Alphabetic # Lo       DEVANAGARI LETTER KA\n094D          ; InCB; Linker # Mn       DEVANAGARI SIGN VIRAMA\n" with
     | .ok [r] => r.lo == 0x094D && r.hi == 0x094D && r.value == Segmentation.InCB.Linker
     | _ => false) = true := by decide
