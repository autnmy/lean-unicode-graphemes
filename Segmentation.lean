/-!
# Segmentation

Unicode text segmentation for Lean 4: extended grapheme clusters as defined by
UAX #29 (https://www.unicode.org/reports/tr29/tr29-49.html).

The library targets one fixed Unicode version and one fixed revision of UAX #29,
recorded below so code and tests read them from a single place.
-/

namespace Segmentation

/-- The Unicode version whose character data the library implements. -/
def unicodeVersion : String := "18.0.0"

/-- The revision of UAX #29 whose grapheme cluster rules the library implements. -/
def uax29Revision : Nat := 49

end Segmentation
