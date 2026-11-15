import Segmentation.Graphemes
import Segmentation.PropsTable

/-!
# Grapheme clusters of a `String.Slice`

`sliceGraphemes` and `sliceBoundaries` segment a `String.Slice` by the same rules as
`Segmentation.graphemes`, but read the slice in place. They build no `List Char` and copy no
text: the clusters are slices of the input, and the cuts are positions in it.

The scan steps through the slice one code point at a time and makes the same decision as
`clustersOf.go` at each step, with the same `ScanState`, `ScanState.push` and `breaksBefore`.
Only the property lookup differs: `charProps` answers an ASCII code point from the small
`asciiProps`, with no table, and any other code point with one search in the combined table
`Tables.propsLookup`. Both are proved equal to `Tables.props`.

The recursion runs on the position in the slice, which moves forward by one code point each
step, so it ends on every input without a step budget.
-/

namespace Segmentation

open GCB in
/-- The properties of the ASCII code point `n` (below 128), read without a table: `CR` and `LF`
are themselves, the other C0 controls and U+007F are `Control`, and every other ASCII code point
is `Other`. No ASCII code point is Extended_Pictographic or has an InCB value. -/
def asciiProps (n : Nat) : Props :=
  { gcb := if n = 0x0D then cr
      else if n = 0x0A then lf
      else if n < 0x20 ∨ n = 0x7F then control
      else other
    extPict := false
    incb := InCB.none }

/-- `asciiProps` gives the same properties as the generated tables, for every code point below
128. -/
theorem asciiProps_eq_props : ∀ n < 128, asciiProps n = Tables.props (Char.ofNat n) := by
  set_option maxRecDepth 20000 in decide

/-- The properties of `c`: `asciiProps` for an ASCII code point, so ASCII text reads no table,
and otherwise one search in the combined table `Tables.propsLookup`. -/
def charProps (c : Char) : Props :=
  if c.toNat < 128 then asciiProps c.toNat else Tables.propsLookup c

/-- `charProps` gives the same properties as `Tables.props`, for every character. -/
theorem charProps_eq_props (c : Char) : charProps c = Tables.props c := by
  unfold charProps
  split
  · rename_i h
    rw [asciiProps_eq_props c.toNat h, Char.ofNat_toNat]
  · exact Tables.propsLookup_eq_props c

/-- The bounds of one cluster in `s`: it runs from `start`, included, to `stop`, excluded. -/
structure ClusterBounds (s : String.Slice) where
  /-- The position of the cluster's first code point. -/
  start : s.Pos
  /-- The position just after the cluster's last code point. -/
  stop : s.Pos
  /-- A cluster never ends before it starts. -/
  start_le_stop : start ≤ stop

/-- The clusters of `s` from the open cluster that starts at `start` onwards, when the code points
from `start` up to `pos` are read and `state` summarises the text read so far. This is
`clustersOf.go` on positions: the open cluster is the bytes from `start` to `pos`. -/
def scanClusters (s : String.Slice) (start pos : s.Pos) (start_le_pos : start ≤ pos)
    (state : ScanState) : List (ClusterBounds s) :=
  if atEnd : pos = s.endPos then [⟨start, pos, start_le_pos⟩]
  else
    let props := charProps (pos.get atEnd)
    have pos_le_next : pos ≤ pos.next atEnd := Std.le_of_lt String.Slice.Pos.lt_next
    if breaksBefore state props then
      ⟨start, pos, start_le_pos⟩ ::
        scanClusters s pos (pos.next atEnd) pos_le_next (state.push props)
    else
      scanClusters s start (pos.next atEnd) (String.Slice.Pos.le_trans start_le_pos pos_le_next)
        (state.push props)
termination_by pos
decreasing_by all_goals exact String.Slice.Pos.lt_next

/-- The bounds of the extended grapheme clusters of `s`, in order; `[]` for an empty slice. -/
def clusterBounds (s : String.Slice) : List (ClusterBounds s) :=
  if empty : s.startPos = s.endPos then []
  else
    scanClusters s s.startPos (s.startPos.next empty)
      (Std.le_of_lt String.Slice.Pos.lt_next)
      (ScanState.start (charProps (s.startPos.get empty)))

/-- The extended grapheme clusters of `s`, by UAX #29 revision 49 and Unicode 18.0.0, as slices
of `s`: no text is copied. `Segmentation.graphemes` gives the same clusters as strings. -/
def sliceGraphemes (s : String.Slice) : List String.Slice :=
  (clusterBounds s).map fun b => s.slice b.start b.stop b.start_le_stop

/-- The boundaries between the extended grapheme clusters of `s`, as positions in `s`, both ends
included; `[s.startPos]` for an empty slice. A position counts bytes from the start of `s`, not
of the string `s` is a slice of. -/
def sliceBoundaries (s : String.Slice) : List s.Pos :=
  s.startPos :: (clusterBounds s).map (·.stop)

end Segmentation
