import Segmentation
import UnicodeExtra

/-!
# The two segmenters, as the benchmark calls them

The only place that calls UnicodeExtra. The comparison needs both libraries' clusters as
`String`s, so UnicodeExtra's slices are copied here. The timed calls count clusters instead, so
each library is timed on its own output: this library's copies are part of its time, and
UnicodeExtra's slices are never copied while it is timed. This library's column checks and times
the reference `List Char` path, `clustersOf`, in one place: `oursClusters`.

`Unicode.graphemeClusters` is walked with `for`, which accepts a list, an array or an iterator,
so this code does not depend on which of them it returns.
-/

namespace Bench

/-- This library's clusters of `text`, from the proved reference on `List Char`. It calls
`clustersOf` directly: compiled calls to `Segmentation.graphemes` run the `String.Slice` scanner,
so going through it would check and time the scanner instead of the reference. -/
def oursClusters (text : String) : List String :=
  (Segmentation.clustersOf Segmentation.Tables.props text.toList).map String.ofList

/-- UnicodeExtra's clusters of `text`, each slice copied into a `String`. -/
def theirsClusters (text : String) : List String := Id.run do
  let mut clusters : Array String := #[]
  for cluster in Unicode.graphemeClusters text do
    clusters := clusters.push cluster.copy
  return clusters.toList

/-- How many clusters this library finds in `text`: the work the benchmark times. -/
def oursClusterCount (text : String) : Nat :=
  (oursClusters text).length

/-- How many clusters UnicodeExtra finds in `text`, without copying any of them. -/
def theirsClusterCount (text : String) : Nat := Id.run do
  let mut count := 0
  for _ in Unicode.graphemeClusters text do
    count := count + 1
  return count

end Bench
