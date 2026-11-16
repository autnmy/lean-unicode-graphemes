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

The scan `scanClusters` steps through the slice one code point at a time and makes the same
decision as `clustersOf.go` at each step. It is a tail-recursive loop: each closed cluster's
bounds are pushed onto an `Array`, and `sliceGraphemes` and `sliceBoundaries` build their list
once from that array. A non-ASCII code point is looked up with one search in the combined table
`Tables.propsLookup`, proved equal to `Tables.props`, decided by `breaksBeforeFast`, one `match`
proved equal to `breaksBefore`, and read with `ScanState.push`. An ASCII code point needs none of
that: `asciiBreaksBefore` decides it from the previous break class and the byte alone, which can
only join it as the LF of CR LF or after a Prepend, and `asciiState` is the state after it. So in
a run of ASCII text only a CR before LF, the first byte of the run after a Prepend, and the first
non-ASCII code point after the run are decided by more than the one byte. `scanClusters_step`
proves both branches equal to the step of `clustersOf.go`.

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

/-- Whether there is a boundary before the ASCII code point `n` (below 128), when the code point
before it has break class `prev`. An ASCII code point has no InCB value and is not
Extended_Pictographic, so GB9c, GB11 and GB12/GB13 never join it, and the verdict needs neither
the scan flags nor a table: a CR, LF or control code point breaks unless it is the LF of CR LF
(GB3, GB4, GB5), and any other ASCII code point breaks unless it follows a Prepend (GB9b). -/
def asciiBreaksBefore (prev : GCB) (n : Nat) : Bool :=
  if n < 0x20 ∨ n = 0x7F then !(prev == .cr && n == 0x0A)
  else prev != .prepend

/-- The scan state after reading the ASCII code point `n` (below 128): its properties, and every
look-back flag clear, since no flag survives a code point that is not InCB Linker or Extend,
Extended_Pictographic, GCB Extend or ZWJ, or a regional indicator. -/
def asciiState (n : Nat) : ScanState :=
  { prev := asciiProps n, linkerTail := false, pictTail := false, zwjAfterPict := false,
    riOdd := false }

/-- `breaksBeforeFast` before an ASCII code point is `asciiBreaksBefore` on the previous break
class, whatever the flags of the state. -/
theorem breaksBeforeFast_asciiProps (s : ScanState) (n : Nat) :
    breaksBeforeFast s (asciiProps n) = asciiBreaksBefore s.prev.gcb n := by
  obtain ⟨⟨prevGcb, _, _⟩, _, _, _, _⟩ := s
  unfold asciiProps asciiBreaksBefore
  by_cases hcr : n = 0x0D <;> by_cases hlf : n = 0x0A <;> by_cases hlow : n < 0x20 <;>
    by_cases hdel : n = 0x7F <;>
    cases prevGcb <;> simp [hcr, hlf, hlow, hdel, breaksBeforeFast, incbIs, isExtPict]

/-- Pushing an ASCII code point gives `asciiState`, whatever the state before it. -/
theorem ScanState.push_asciiProps (s : ScanState) (n : Nat) :
    s.push (asciiProps n) = asciiState n := by
  unfold ScanState.push asciiState asciiProps
  by_cases hcr : n = 0x0D <;> by_cases hlf : n = 0x0A <;> by_cases hlow : n < 0x20 <;>
    by_cases hdel : n = 0x7F <;>
    simp [hcr, hlf, hlow, hdel, incbIs, isExtPict, gcbIn]

/-- The bounds of one cluster in `s`: it runs from `start`, included, to `stop`, excluded. -/
structure ClusterBounds (s : String.Slice) where
  /-- The position of the cluster's first code point. -/
  start : s.Pos
  /-- The position just after the cluster's last code point. -/
  stop : s.Pos
  /-- A cluster never ends before it starts. -/
  start_le_stop : start ≤ stop

/-- `acc` followed by the clusters of `s` from the open cluster that starts at `start` onwards,
when the code points from `start` up to `pos` are read and `state` summarises the text read so
far. This is `clustersOf.go` on positions: the open cluster is the bytes from `start` to `pos`,
and each closed cluster is pushed onto `acc`, so every recursive call is a tail call.

An ASCII code point is decided by `asciiBreaksBefore` and read into `asciiState`, with no
property lookup; any other code point is looked up once in `Tables.propsLookup` and decided by
`breaksBeforeFast`. `scanClusters_step` proves both branches are the step of `charProps`,
`breaksBeforeFast` and `ScanState.push`. -/
def scanClusters (s : String.Slice) (start pos : s.Pos) (start_le_pos : start ≤ pos)
    (state : ScanState) (acc : Array (ClusterBounds s)) : Array (ClusterBounds s) :=
  if atEnd : pos = s.endPos then acc.push ⟨start, pos, start_le_pos⟩
  else
    let c := pos.get atEnd
    have pos_le_next : pos ≤ pos.next atEnd := Std.le_of_lt String.Slice.Pos.lt_next
    have start_le_next : start ≤ pos.next atEnd :=
      String.Slice.Pos.le_trans start_le_pos pos_le_next
    if c.toNat < 128 then
      if asciiBreaksBefore state.prev.gcb c.toNat then
        scanClusters s pos (pos.next atEnd) pos_le_next (asciiState c.toNat)
          (acc.push ⟨start, pos, start_le_pos⟩)
      else
        scanClusters s start (pos.next atEnd) start_le_next (asciiState c.toNat) acc
    else
      let props := Tables.propsLookup c
      if breaksBeforeFast state props then
        scanClusters s pos (pos.next atEnd) pos_le_next (state.push props)
          (acc.push ⟨start, pos, start_le_pos⟩)
      else
        scanClusters s start (pos.next atEnd) start_le_next (state.push props) acc
termination_by pos
decreasing_by all_goals exact String.Slice.Pos.lt_next

/-- One step of `scanClusters` before the end of the slice is the step of `clustersOf.go`: look up
the next code point with `charProps`, decide with `breaksBeforeFast`, and read it with
`ScanState.push`. -/
theorem scanClusters_step (s : String.Slice) (start pos : s.Pos) (start_le_pos : start ≤ pos)
    (state : ScanState) (acc : Array (ClusterBounds s)) (atEnd : pos ≠ s.endPos) :
    scanClusters s start pos start_le_pos state acc =
      if breaksBeforeFast state (charProps (pos.get atEnd)) then
        scanClusters s pos (pos.next atEnd) (Std.le_of_lt String.Slice.Pos.lt_next)
          (state.push (charProps (pos.get atEnd))) (acc.push ⟨start, pos, start_le_pos⟩)
      else
        scanClusters s start (pos.next atEnd)
          (String.Slice.Pos.le_trans start_le_pos (Std.le_of_lt String.Slice.Pos.lt_next))
          (state.push (charProps (pos.get atEnd))) acc := by
  rw [scanClusters, dite_eq_right atEnd]
  unfold charProps
  by_cases ascii : (pos.get atEnd).toNat < 128
  · simp only [ascii, ↓reduceIte, breaksBeforeFast_asciiProps, ScanState.push_asciiProps]
  · simp only [ascii, ↓reduceIte]

/-- The bounds of the extended grapheme clusters of `s`, in order; empty for an empty slice. -/
def clusterBounds (s : String.Slice) : Array (ClusterBounds s) :=
  if empty : s.startPos = s.endPos then #[]
  else
    scanClusters s s.startPos (s.startPos.next empty)
      (Std.le_of_lt String.Slice.Pos.lt_next)
      (ScanState.start (charProps (s.startPos.get empty))) #[]

/-- The extended grapheme clusters of `s`, by UAX #29 revision 49 and Unicode 18.0.0, as slices
of `s`: no text is copied. `Segmentation.graphemes` gives the same clusters as strings. The list
is built once, straight from the array of cluster bounds. -/
def sliceGraphemes (s : String.Slice) : List String.Slice :=
  (clusterBounds s).foldr (fun b rest => s.slice b.start b.stop b.start_le_stop :: rest) []

/-- The boundaries between the extended grapheme clusters of `s`, as positions in `s`, both ends
included; `[s.startPos]` for an empty slice. A position counts bytes from the start of `s`, not
of the string `s` is a slice of. -/
def sliceBoundaries (s : String.Slice) : List s.Pos :=
  s.startPos :: (clusterBounds s).foldr (fun b rest => b.stop :: rest) []

/-- `sliceGraphemes` maps each cluster's bounds to its slice of `s`. -/
theorem sliceGraphemes_eq_map (s : String.Slice) :
    sliceGraphemes s =
      (clusterBounds s).toList.map fun b => s.slice b.start b.stop b.start_le_stop := by
  rw [sliceGraphemes, ← Array.foldr_toList, List.map_eq_foldr]

/-- `sliceBoundaries` is the slice's start followed by each cluster's end. -/
theorem sliceBoundaries_eq_map (s : String.Slice) :
    sliceBoundaries s = s.startPos :: (clusterBounds s).toList.map (·.stop) := by
  rw [sliceBoundaries, ← Array.foldr_toList, List.map_eq_foldr]

/-! ### Agreement with the reference -/

/-- `scanClusters` follows `clustersOf.go`. When `start` splits the text of `s` after the code
points `read`, and `pos` splits it after `read ++ cluster` with `rest` still to read, the scan
keeps `acc` and appends clusters `out` to it; `out` reads back as the clusters `clustersOf.go`
returns from the open cluster `cluster`, and the byte offsets of `start` and of each cluster's
end are the running sums of the UTF-8 sizes of those clusters, starting from the size of
`read`. -/
theorem scanClusters_agree (s : String.Slice) :
    ∀ (rest : List Char) (start pos : s.Pos) (start_le_pos : start ≤ pos) (state : ScanState)
      (acc : Array (ClusterBounds s)) (read cluster : List Char),
      start.Splits (String.ofList read) (String.ofList (cluster ++ rest)) →
      pos.Splits (String.ofList (read ++ cluster)) (String.ofList rest) →
      ∃ out : List (ClusterBounds s),
        (scanClusters s start pos start_le_pos state acc).toList = acc.toList ++ out ∧
        out.map (fun b => (s.slice b.start b.stop b.start_le_stop).copy) =
          (clustersOf.go charProps state cluster.reverse rest).map String.ofList ∧
        (String.ofList read).utf8ByteSize :: out.map (·.stop.offset.byteIdx) =
          ((clustersOf.go charProps state cluster.reverse rest).map
            (fun g => (String.ofList g).utf8ByteSize)).scanl (· + ·)
            (String.ofList read).utf8ByteSize
  | [], start, pos, start_le_pos, state, acc, read, cluster, hstart, hpos => by
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
    rw [scanClusters, dite_eq_left atEnd]
    refine ⟨[⟨start, pos, start_le_pos⟩], Array.toList_push, ?_, ?_⟩ <;>
      simp [clustersOf.go, hcopy, hoff]
  | c :: rest, start, pos, start_le_pos, state, acc, read, cluster, hstart, hpos => by
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
    rw [scanClusters_step s start pos start_le_pos state acc atEnd]
    simp only [hget, breaksBeforeFast_eq_breaksBefore]
    unfold clustersOf.go
    by_cases hb : breaksBefore state (charProps c) = true
    · simp only [hb, ↓reduceIte]
      obtain ⟨out, hout, ih₁, ih₂⟩ := scanClusters_agree s rest pos (pos.next atEnd) _
        (state.push (charProps c)) (acc.push ⟨start, pos, start_le_pos⟩) (read ++ cluster) [c]
        hpos hnext
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append] at ih₁ ih₂
      refine ⟨⟨start, pos, start_le_pos⟩ :: out, ?_, ?_, ?_⟩
      · rw [hout, Array.toList_push, List.append_assoc, List.singleton_append]
      · rw [List.map_cons, hcopy, ih₁, List.reverse_reverse, List.map_cons]
      · rw [List.map_cons, hoff, ih₂, List.reverse_reverse, List.map_cons, List.scanl_cons,
          String.ofList_append, String.utf8ByteSize_append]
    · simp only [hb, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨out, hout, ih₁, ih₂⟩ := scanClusters_agree s rest start (pos.next atEnd) _
        (state.push (charProps c)) acc read (cluster ++ [c])
        (by rw [List.append_assoc]; exact hstart)
        (by rw [← List.append_assoc]; exact hnext)
      simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
        List.singleton_append] at ih₁ ih₂
      exact ⟨out, hout, ih₁, ih₂⟩

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
  rw [← funext charProps_eq_props, sliceGraphemes_eq_map, sliceBoundaries_eq_map]
  unfold clusterBounds
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
    obtain ⟨out, hout, ih₁, ih₂⟩ := scanClusters_agree s rest s.startPos (s.startPos.next empty) _
      (ScanState.start (charProps c)) #[] [] [c] hstart hnext
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, String.ofList_nil,
      String.utf8ByteSize_empty] at ih₁ ih₂
    simp only [List.nil_append] at hout
    rw [hget, hout]
    simp only [hcs, clustersOf]
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
