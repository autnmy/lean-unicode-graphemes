import Segmentation.Statements
import Segmentation.Version
import Segmentation.Tables
import Segmentation.TableLookup
import Segmentation.RangeLookup
import Segmentation.Graphemes
import Segmentation.Partition
import Segmentation.ScanInvariants
import Segmentation.Cuts

/-!
# Segmentation

Unicode text segmentation for Lean 4: extended grapheme clusters as defined by
UAX #29 (https://www.unicode.org/reports/tr29/tr29-49.html).

The library targets one fixed Unicode version and one fixed revision of UAX #29,
recorded in `Segmentation.Version` so code and tests read them from a single place.
-/
