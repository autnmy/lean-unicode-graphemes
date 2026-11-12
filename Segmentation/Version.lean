/-!
# Version

The Unicode version and UAX #29 revision the library implements, recorded here
so code and tests read them from a single place. This module imports nothing
from the library, so the table generator can read the version without
building the generated tables it writes.
-/

namespace Segmentation

/-- The Unicode version whose character data the library implements. -/
def unicodeVersion : String := "18.0.0"

/-- The revision of UAX #29 whose grapheme cluster rules the library implements. -/
def uax29Revision : Nat := 49

end Segmentation
