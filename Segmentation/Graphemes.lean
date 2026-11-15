import Segmentation.Statements
import Segmentation.Tables

/-!
# Grapheme cluster segmentation

Splits text into extended grapheme clusters by the rules of UAX #29 revision 49, in one pass
over the code points.

Most rules read only the code point before a position and the one after it. GB9c, GB11 and
GB12/GB13 read further back, so the pass carries a few flags that summarise the text read so
far (`ScanState`). The decision at each position is the table `breakRows`, in the order of
`Segmentation.rules`: the first row that applies gives the verdict, and GB999 (break) is the
fallback. GB1 and GB2, the breaks at the start and end of the text, are the ends of the list.

The core, `clustersOf` and `cutsOf`, works over `List Char` and takes the property lookup as a
parameter, like the statements in `Segmentation.Statements`. `graphemes` and `boundaries` pass
it the generated tables, `Segmentation.Tables.props`, and convert between `String` and
`List Char`.
-/

namespace Segmentation

/-- What the rules that look back further than one code point need to know about the text
read so far. -/
structure ScanState where
  /-- The properties of the last code point read. -/
  prev : Props
  /-- The text ends with InCB `Linker` then InCB `Extend*` (left side of GB9c). -/
  linkerTail : Bool
  /-- The text ends with an Extended_Pictographic code point then GCB `Extend*`. -/
  pictTail : Bool
  /-- The text ends with Extended_Pictographic, GCB `Extend*`, GCB `ZWJ` (left side of GB11). -/
  zwjAfterPict : Bool
  /-- The run of GCB `RI` at the end of the text has odd length (left side of GB12 and GB13). -/
  riOdd : Bool

/-- The state after reading one more code point with properties `p`. Any code point outside a
run clears that run's flag, so a ZWJ or a mark between regional indicators restarts the count. -/
def ScanState.push (s : ScanState) (p : Props) : ScanState where
  prev := p
  linkerTail := incbIs .linker p || (s.linkerTail && incbIs .extend p)
  pictTail := isExtPict p || (s.pictTail && gcbIn [.extend] p)
  zwjAfterPict := s.pictTail && gcbIn [.zwj] p
  riOdd := gcbIn [.regionalIndicator] p && !s.riOdd

/-- The state after the first code point of the text. Before it no run has started, so every
flag starts false; `prev` is replaced by `push`. -/
def ScanState.start (p : Props) : ScanState :=
  ScanState.push ⟨p, false, false, false, false⟩ p

/-- One row of the decision table: when `applies` holds for the state before a position and the
code point after it, `breaks` is the verdict there. -/
structure BreakRow where
  name : String
  applies : ScanState → Props → Bool
  breaks : Bool

open GCB in
/-- The rules GB3 to GB13 of `Segmentation.rules`, in the same order. GB12 and GB13 share a row:
together they say an odd run of regional indicators before the position joins the next one. -/
def breakRows : List BreakRow := [
  ⟨"GB3",  fun s n => gcbIn [cr] s.prev && gcbIn [lf] n,                     false⟩,
  ⟨"GB4",  fun s _ => gcbIn [control, cr, lf] s.prev,                         true⟩,
  ⟨"GB5",  fun _ n => gcbIn [control, cr, lf] n,                              true⟩,
  ⟨"GB6",  fun s n => gcbIn [l] s.prev && gcbIn [l, v, lv, lvt] n,            false⟩,
  ⟨"GB7",  fun s n => gcbIn [lv, v] s.prev && gcbIn [v, t] n,                 false⟩,
  ⟨"GB8",  fun s n => gcbIn [lvt, t] s.prev && gcbIn [t] n,                   false⟩,
  ⟨"GB9",  fun _ n => gcbIn [extend, zwj] n,                                  false⟩,
  ⟨"GB9a", fun _ n => gcbIn [spacingMark] n,                                  false⟩,
  ⟨"GB9b", fun s _ => gcbIn [prepend] s.prev,                                 false⟩,
  ⟨"GB9c", fun s n => s.linkerTail && incbIs .consonant n,                    false⟩,
  ⟨"GB11", fun s n => s.zwjAfterPict && isExtPict n,                          false⟩,
  ⟨"GB12, GB13", fun s n => s.riOdd && gcbIn [regionalIndicator] n,           false⟩ ]

/-- Whether there is a boundary between the text summarised by `s` and a next code point with
properties `next`: the verdict of the first row that applies, else GB999's break. -/
def breaksBefore (s : ScanState) (next : Props) : Bool :=
  match breakRows.find? (·.applies s next) with
  | some row => row.breaks
  | none => true

/-- The extended grapheme clusters of `cs`, with `props` as the property lookup. -/
def clustersOf (props : Char → Props) : List Char → List (List Char)
  | [] => []
  | c :: rest => go (ScanState.start (props c)) [c] rest
where
  /-- `cluster` is the open cluster, newest code point first. -/
  go (s : ScanState) (cluster : List Char) : List Char → List (List Char)
    | [] => [cluster.reverse]
    | c :: rest =>
      let p := props c
      if breaksBefore s p then cluster.reverse :: go (s.push p) [c] rest
      else go (s.push p) (c :: cluster) rest

/-- The positions between the clusters of `cs`, counted in code points from the start, both
ends included; `[0]` for the empty list. -/
def cutsOf (props : Char → Props) (cs : List Char) : List Nat :=
  ((clustersOf props cs).map List.length).scanl (· + ·) 0

/-- The extended grapheme clusters of `s`, by UAX #29 revision 49 and Unicode 18.0.0. -/
def graphemes (s : String) : List String :=
  (clustersOf Tables.props s.toList).map String.ofList

/-- The boundaries between the extended grapheme clusters of `s`, counted in code points from
the start, both ends included; `[0]` for the empty string. -/
def boundaries (s : String) : List Nat :=
  cutsOf Tables.props s.toList

end Segmentation
