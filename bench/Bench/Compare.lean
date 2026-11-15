import Bench.Inputs

/-!
# Comparing the two libraries' clusters

Timing two segmenters only means something when they return the same clusters, so the benchmark
compares them on every input first and stops at the first difference. The comparison walks both
lists to the end of the longer one: a check that zipped them would stop at the shorter list and
miss a cluster that only one library returns.
-/

namespace Bench

/-- Where two cluster lists first differ. `ours` or `theirs` is `none` when that list has
already ended at `index`. -/
structure Difference where
  input : String
  index : Nat
  ours : Option String
  theirs : Option String
  deriving DecidableEq, Repr

/-- The first index at which `ours` and `theirs` differ, counting from `start`. -/
private def firstDifferenceFrom (inputName : String) :
    Nat → List String → List String → Option Difference
  | _, [], [] => none
  | start, o :: _, [] => some { input := inputName, index := start, ours := some o, theirs := none }
  | start, [], t :: _ => some { input := inputName, index := start, ours := none, theirs := some t }
  | start, o :: os, t :: ts =>
    if o = t then firstDifferenceFrom inputName (start + 1) os ts
    else some { input := inputName, index := start, ours := some o, theirs := some t }

/-- The first cluster at which this library's clusters (`ours`) and UnicodeExtra's (`theirs`)
differ on the input named `inputName`, or `none` when the lists are equal. -/
def firstDifference (inputName : String) (ours theirs : List String) : Option Difference :=
  firstDifferenceFrom inputName 0 ours theirs

/-- The first difference between the two segmenters over `inputs`, taken in list order. -/
def checkAll (ours theirs : String → List String) : List NamedInput → Option Difference
  | [] => none
  | i :: rest =>
    match firstDifference i.name (ours i.text) (theirs i.text) with
    | some d => some d
    | none => checkAll ours theirs rest

/-- The process exit status for a comparison: 1 fails the CI job when the libraries disagree. -/
def exitCodeFor : Option Difference → UInt32
  | none => 0
  | some _ => 1

end Bench
