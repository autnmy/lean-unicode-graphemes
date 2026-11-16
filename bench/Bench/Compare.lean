import Bench.Inputs

/-!
# Comparing the three segmenters' clusters

Timing segmenters only means something when they return the same clusters, so the benchmark
compares this library's reference segmenter, UnicodeExtra and this library's fast segmenter on
every input first, and stops at the first difference. The comparison walks the lists to the end
of the longest one: a check that zipped them would stop at the shortest list and miss a cluster
that only one segmenter returns.
-/

namespace Bench

/-- Where three cluster lists first differ. `ours`, `theirs` or `fast` is `none` when that list
has already ended at `index`. -/
structure Difference where
  input : String
  index : Nat
  ours : Option String
  theirs : Option String
  fast : Option String
  deriving DecidableEq, Repr

/-- The first index at which `ours`, `theirs` and `fast` are not all present and equal, counting
from `start`. Plain structural recursion on the lists, so `decide` can evaluate it. -/
private def firstDifferenceFrom (inputName : String) :
    Nat → List String → List String → List String → Option Difference
  | _, [], [], [] => none
  | start, o :: os, t :: ts, f :: fs =>
    if o = t ∧ t = f then firstDifferenceFrom inputName (start + 1) os ts fs
    else some { input := inputName, index := start, ours := some o, theirs := some t,
                fast := some f }
  -- At least one list has ended and at least one has not, so the lists differ here.
  | start, os, ts, fs =>
    some { input := inputName, index := start, ours := os.head?, theirs := ts.head?,
           fast := fs.head? }

/-- The first cluster at which this library's clusters (`ours`), UnicodeExtra's (`theirs`) and
this library's fast segmenter's (`fast`) are not all equal on the input named `inputName`, or
`none` when the three lists are equal. -/
def firstDifference (inputName : String) (ours theirs fast : List String) : Option Difference :=
  firstDifferenceFrom inputName 0 ours theirs fast

/-- The first difference between the three segmenters over `inputs`, taken in list order. -/
def checkAll (ours theirs fast : String → List String) : List NamedInput → Option Difference
  | [] => none
  | i :: rest =>
    match firstDifference i.name (ours i.text) (theirs i.text) (fast i.text) with
    | some d => some d
    | none => checkAll ours theirs fast rest

/-- The process exit status for a comparison: 1 fails the CI job when the segmenters disagree. -/
def exitCodeFor : Option Difference → UInt32
  | none => 0
  | some _ => 1

end Bench
