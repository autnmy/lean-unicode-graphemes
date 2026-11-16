import Segmentation.Graphemes
import Segmentation.Partition
import Segmentation.PropsTable
import Segmentation.Cuts
import Segmentation.Rules

/-!
# Grapheme clusters of a `String.Slice`

`sliceGraphemes` and `sliceBoundaries` segment a `String.Slice` by the same rules as
`Segmentation.graphemes`, but read the slice in place. They build no `List Char` and copy no
text: the clusters are slices of the input, and the cuts are positions in it.

The scan steps through the slice one code point at a time and makes the same decision as
`clustersOf.go` at each step, with the same `ScanState` and `ScanState.push`. Two things differ.
The property lookup `charProps` answers an ASCII code point from the small `asciiProps`, with no
table, and any other code point with one search in the combined table `Tables.propsLookup`; both
are proved equal to `Tables.props`. The break decision `breaksBeforeFast` is one `match` on the
two break classes instead of a search through `breakRows`, and is proved equal to `breaksBefore`.

The recursion runs on the position in the slice, which moves forward by one code point each
step, so it ends on every input without a step budget.

`sliceGraphemes_agree` proves that, on the whole of any string, the clusters read back as
`graphemes` and the cuts are the byte offsets of `boundaries`. The proof follows the scan and
`clustersOf.go` step by step: at every step the position splits the text into the code points
read so far and the rest, so its byte offset is the UTF-8 size of what was read.

`graphemesFast` and `boundariesFast` give the scanner the types of `graphemes` and `boundaries`.
They are proved equal to them and registered with `csimp`, so compiled code that calls the
reference runs the scanner, and the four statements of `Segmentation.Statements` are proved for
them by rewriting into the reference's proofs.
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

/-- Whether there is a boundary between the text summarised by `s` and a next code point with
properties `next`, decided by one `match` on the two break classes instead of a search through
`breakRows`. The arms keep the order of `breakRows`, so the first rule that applies decides, and
a break is the default (GB999). -/
def breaksBeforeFast (s : ScanState) (next : Props) : Bool :=
  match s.prev.gcb, next.gcb with
  -- GB3
  | .cr, .lf => false
  -- GB4, GB5
  | .cr, _ | .lf, _ | .control, _ => true
  | _, .cr | _, .lf | _, .control => true
  -- GB6, GB7, GB8
  | .l, .l | .l, .v | .l, .lv | .l, .lvt => false
  | .lv, .v | .lv, .t | .v, .v | .v, .t => false
  | .lvt, .t | .t, .t => false
  -- GB9, GB9a
  | _, .extend | _, .zwj | _, .spacingMark => false
  -- GB9b
  | .prepend, _ => false
  | _, _ =>
    -- GB9c
    if s.linkerTail && incbIs .consonant next then false
    -- GB11
    else if s.zwjAfterPict && isExtPict next then false
    -- GB12, GB13
    else if s.riOdd && next.gcb == .regionalIndicator then false
    else true

/-- `breaksBefore` read as a chain of `if`s over `breakRows`, one per row in order, ending in a
break. In this form `simp` can compare it with the `match` of `breaksBeforeFast`. -/
private theorem breaksBefore_eq_foldr (s : ScanState) (next : Props) :
    breaksBefore s next =
      breakRows.foldr (fun row rest => if row.applies s next then row.breaks else rest) true := by
  unfold breaksBefore
  generalize breakRows = rows
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    rw [List.find?_cons, List.foldr_cons]
    cases row.applies s next <;> simp [ih]

/-- `breaksBeforeFast` makes the same decision as `breaksBefore`, for every state and every next
code point. -/
theorem breaksBeforeFast_eq_breaksBefore :
    ∀ s next, breaksBeforeFast s next = breaksBefore s next := by
  intro s next
  rw [breaksBefore_eq_foldr]
  obtain ⟨⟨prevGcb, _, _⟩, _, _, _, _⟩ := s
  obtain ⟨nextGcb, _, _⟩ := next
  cases prevGcb <;> cases nextGcb <;>
    simp [breaksBeforeFast, breakRows, gcbIn, incbIs, isExtPict]

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
    if breaksBeforeFast state props then
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

/-! ### Agreement with the reference -/

/-- `scanClusters` follows `clustersOf.go`. When `start` splits the text of `s` after the code
points `read`, and `pos` splits it after `read ++ cluster` with `rest` still to read, the clusters
the scan returns read back as the clusters `clustersOf.go` returns from the open cluster
`cluster`, and the byte offsets of `start` and of each cluster's end are the running sums of the
UTF-8 sizes of those clusters, starting from the size of `read`. -/
theorem scanClusters_agree (s : String.Slice) :
    ∀ (rest : List Char) (start pos : s.Pos) (start_le_pos : start ≤ pos) (state : ScanState)
      (read cluster : List Char),
      start.Splits (String.ofList read) (String.ofList (cluster ++ rest)) →
      pos.Splits (String.ofList (read ++ cluster)) (String.ofList rest) →
      (scanClusters s start pos start_le_pos state).map
          (fun b => (s.slice b.start b.stop b.start_le_stop).copy) =
        (clustersOf.go charProps state cluster.reverse rest).map String.ofList ∧
      (String.ofList read).utf8ByteSize ::
          (scanClusters s start pos start_le_pos state).map (·.stop.offset.byteIdx) =
        ((clustersOf.go charProps state cluster.reverse rest).map
          (fun g => (String.ofList g).utf8ByteSize)).scanl (· + ·) (String.ofList read).utf8ByteSize
  | [], start, pos, start_le_pos, state, read, cluster, hstart, hpos => by
    rw [List.append_nil] at hstart
    rw [String.ofList_nil] at hpos
    have atEnd : pos = s.endPos := hpos.eq_endPos_iff.mpr rfl
    have hcopy : (s.slice start pos start_le_pos).copy = String.ofList cluster := by
      obtain ⟨_, h⟩ := String.Slice.copy_slice_eq_iff_splits.mpr
        ⟨String.ofList read, "", by rwa [String.append_empty],
          by rwa [← String.ofList_append]⟩
      exact h
    have hoff : pos.offset.byteIdx = (String.ofList (read ++ cluster)).utf8ByteSize := by
      rw [hpos.offset_eq_rawEndPos, String.byteIdx_rawEndPos]
    rw [scanClusters]
    split
    · simp [clustersOf.go, hcopy, hoff]
    · contradiction
  | c :: rest, start, pos, start_le_pos, state, read, cluster, hstart, hpos => by
    have hpos' : pos.Splits (String.ofList (read ++ cluster))
        (String.singleton c ++ String.ofList rest) := by
      rwa [String.ofList_cons] at hpos
    have atEnd : pos ≠ s.endPos := hpos'.ne_endPos_of_singleton
    have hnext' : (pos.next atEnd).Splits (String.ofList (read ++ cluster) ++ String.singleton c)
        (String.ofList rest) := hpos'.next
    have hget : pos.get atEnd = c := hnext'.get_eq_of_singleton
    have hnext : (pos.next atEnd).Splits (String.ofList ((read ++ cluster) ++ [c]))
        (String.ofList rest) := by
      rw [String.ofList_append, ← String.singleton_eq_ofList]
      exact hnext'
    have hcopy : (s.slice start pos start_le_pos).copy = String.ofList cluster := by
      obtain ⟨_, h⟩ := String.Slice.copy_slice_eq_iff_splits.mpr
        ⟨String.ofList read, String.ofList (c :: rest), by rwa [← String.ofList_append],
          by rwa [← String.ofList_append]⟩
      exact h
    have hoff : pos.offset.byteIdx = (String.ofList (read ++ cluster)).utf8ByteSize := by
      rw [hpos.offset_eq_rawEndPos, String.byteIdx_rawEndPos]
    rw [scanClusters]
    split
    · contradiction
    simp only [hget, breaksBeforeFast_eq_breaksBefore]
    unfold clustersOf.go
    by_cases hb : breaksBefore state (charProps c) = true
    · simp only [hb, ↓reduceIte]
      obtain ⟨ih₁, ih₂⟩ := scanClusters_agree s rest pos (pos.next atEnd) _
        (state.push (charProps c)) (read ++ cluster) [c] hpos hnext
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append] at ih₁ ih₂
      refine ⟨?_, ?_⟩
      · rw [List.map_cons, hcopy, ih₁, List.reverse_reverse, List.map_cons]
      · rw [List.map_cons, hoff, ih₂, List.reverse_reverse, List.map_cons, List.scanl_cons,
          String.ofList_append, String.utf8ByteSize_append]
    · simp only [hb, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨ih₁, ih₂⟩ := scanClusters_agree s rest start (pos.next atEnd) _
        (state.push (charProps c)) read (cluster ++ [c])
        (by rw [List.append_assoc]; exact hstart)
        (by rw [← List.append_assoc]; exact hnext)
      simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
        List.singleton_append] at ih₁ ih₂
      exact ⟨ih₁, ih₂⟩

/-- The UTF-8 sizes of the prefixes of `pre ++ clusters.flatten` that end at the code-point cuts
between `clusters` are the running sums of the clusters' UTF-8 sizes, starting from `pre`'s. -/
theorem scanl_utf8ByteSize_take (clusters : List (List Char)) (pre : List Char) :
    ((clusters.map List.length).scanl (· + ·) pre.length).map
        (fun n => (String.ofList ((pre ++ clusters.flatten).take n)).utf8ByteSize) =
      (clusters.map (fun g => (String.ofList g).utf8ByteSize)).scanl (· + ·)
        (String.ofList pre).utf8ByteSize := by
  induction clusters generalizing pre with
  | nil => simp
  | cons g clusters ih =>
    have := ih (pre ++ g)
    simp only [List.length_append, List.append_assoc, String.ofList_append,
      String.utf8ByteSize_append] at this
    simp [List.scanl_cons, this]

/-- On any slice, `sliceGraphemes` and `sliceBoundaries` agree with `clustersOf` on its text: the
clusters read back as its clusters, and the cuts sit at the running sums of their UTF-8 sizes. -/
theorem sliceGraphemes_agree_clustersOf (s : String.Slice) :
    (sliceGraphemes s).map String.Slice.copy =
        (clustersOf Tables.props s.copy.toList).map String.ofList ∧
      (sliceBoundaries s).map (fun p => p.offset.byteIdx) =
        ((clustersOf Tables.props s.copy.toList).map
          (fun g => (String.ofList g).utf8ByteSize)).scanl (· + ·) 0 := by
  rw [← funext charProps_eq_props]
  unfold sliceGraphemes sliceBoundaries clusterBounds
  split
  · rename_i empty
    have : s.copy = "" := (s.splits_startPos.eq_endPos_iff).mp empty
    simp [this, clustersOf]
  · rename_i empty
    obtain ⟨c, rest, hcs⟩ : ∃ c rest, s.copy.toList = c :: rest := by
      cases h : s.copy.toList with
      | nil =>
        exact absurd ((s.splits_startPos.eq_endPos_iff).mpr (String.toList_eq_nil_iff.mp h)) empty
      | cons c rest => exact ⟨c, rest, rfl⟩
    have hstart : s.startPos.Splits (String.ofList []) (String.ofList ([] ++ c :: rest)) := by
      rw [String.ofList_nil, List.nil_append, ← hcs, String.ofList_toList]
      exact s.splits_startPos
    have hstart' : s.startPos.Splits "" (String.singleton c ++ String.ofList rest) := by
      rwa [String.ofList_nil, List.nil_append, String.ofList_cons] at hstart
    have hnext' := hstart'.next
    have hget : s.startPos.get empty = c := hnext'.get_eq_of_singleton
    have hnext : (s.startPos.next empty).Splits (String.ofList ([] ++ [c])) (String.ofList rest) := by
      rw [List.nil_append, ← String.singleton_eq_ofList]
      rw [String.empty_append] at hnext'
      exact hnext'
    obtain ⟨ih₁, ih₂⟩ := scanClusters_agree s rest s.startPos (s.startPos.next empty) _
      (ScanState.start (charProps c)) [] [c] hstart hnext
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, String.ofList_nil,
      String.utf8ByteSize_empty] at ih₁ ih₂
    simp only [hget, hcs, clustersOf]
    refine ⟨?_, ?_⟩
    · rw [List.map_map]
      exact ih₁
    · rw [List.map_cons, List.map_map, String.Slice.offset_startPos, String.Pos.Raw.byteIdx_zero]
      exact ih₂

/-- The clusters of `sliceGraphemes`, read back as strings, are exactly `graphemes s`, and the
cuts of `sliceBoundaries`, as byte offsets, are `boundaries s` with each code-point cut `n` mapped
to the UTF-8 size of the first `n` code points of `s`. -/
theorem sliceGraphemes_agree (s : String) :
    (sliceGraphemes s.toSlice).map String.Slice.copy = graphemes s ∧
      (sliceBoundaries s.toSlice).map (fun p => p.offset.byteIdx) =
        (boundaries s).map (fun n => (String.ofList (s.toList.take n)).utf8ByteSize) := by
  obtain ⟨h₁, h₂⟩ := sliceGraphemes_agree_clustersOf s.toSlice
  rw [String.copy_toSlice] at h₁ h₂
  refine ⟨h₁, ?_⟩
  have := scanl_utf8ByteSize_take (clustersOf Tables.props s.toList) []
  simp only [List.length_nil, List.nil_append, clustersOf_flatten, String.ofList_nil,
    String.utf8ByteSize_empty] at this
  rw [h₂, boundaries, cutsOf, this]

/-! ### The fast segmenter on `String` -/

/-- The extended grapheme clusters of `s`, read by the slice scanner `sliceGraphemes` and copied
into strings. Proved equal to `graphemes` by `graphemes_eq_graphemesFast`, which makes compiled
calls to `graphemes` run this. -/
def graphemesFast (s : String) : List String :=
  (sliceGraphemes s.toSlice).map String.Slice.copy

/-- The positions between the clusters of `graphemesFast s`, counted in code points from the
start, both ends included: the running sums, from 0, of the clusters' lengths. Proved equal to
`boundaries` by `boundaries_eq_boundariesFast`, which makes compiled calls to `boundaries` run
this. -/
def boundariesFast (s : String) : List Nat :=
  ((graphemesFast s).map String.length).scanl (· + ·) 0

/-- `graphemesFast` is `graphemes`. Registered with `csimp`, so compiled code that calls
`graphemes` runs the slice scanner; the kernel still reduces `graphemes` itself. -/
@[csimp]
theorem graphemes_eq_graphemesFast : @graphemes = @graphemesFast :=
  funext fun s => ((sliceGraphemes_agree s).1).symm

/-- `BoundariesMatchCuts` for `graphemesFast` and `boundariesFast`: `boundariesFast` lists the cut
points of `graphemesFast`. -/
theorem boundariesFast_agree : BoundariesMatchCuts graphemesFast boundariesFast :=
  fun _ => rfl

/-- `boundariesFast` is `boundaries`. Registered with `csimp`, so compiled code that calls
`boundaries` runs the slice scanner. -/
@[csimp]
theorem boundaries_eq_boundariesFast : @boundaries = @boundariesFast := by
  funext s
  rw [boundaries_agree s, boundariesFast_agree s, graphemes_eq_graphemesFast]

/-- `JoinRestoresInput` for `graphemesFast`: the clusters joined back together are the input. -/
theorem graphemesFast_join : JoinRestoresInput graphemesFast := by
  rw [← graphemes_eq_graphemesFast]
  exact graphemes_join

/-- `ClustersNonEmpty` for `graphemesFast`: no cluster is the empty string. -/
theorem graphemesFast_ne_empty : ClustersNonEmpty graphemesFast := by
  rw [← graphemes_eq_graphemesFast]
  exact graphemes_ne_empty

/-- `CutsMatchRules` for `graphemesFast`: on a non-empty string, a position is a cut point of
`graphemesFast` exactly when UAX #29 puts a boundary there. -/
theorem graphemesFast_rules : CutsMatchRules Tables.props graphemesFast := by
  rw [← graphemes_eq_graphemesFast]
  exact graphemes_rules

end Segmentation
