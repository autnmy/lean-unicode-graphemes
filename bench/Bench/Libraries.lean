import Segmentation
import UnicodeExtra

/-!
# The two segmenters, as the benchmark calls them

The only place that calls UnicodeExtra. The comparison needs both libraries' clusters as
`String`s, so UnicodeExtra's slices are copied here. The timed calls count clusters instead, so
each library is timed on its own output: this library's copies are part of its time, and
UnicodeExtra's slices are never copied while it is timed.

`Unicode.graphemeClusters` is walked with `for`, which accepts a list, an array or an iterator,
so this code does not depend on which of them it returns.
-/

namespace Bench

/-- This library's clusters of `text`. -/
def oursClusters (text : String) : List String :=
  Segmentation.graphemes text

/-- UnicodeExtra's clusters of `text`, each slice copied into a `String`. -/
def theirsClusters (text : String) : List String := Id.run do
  let mut clusters : Array String := #[]
  for cluster in Unicode.graphemeClusters text do
    clusters := clusters.push cluster.copy
  return clusters.toList

/-- How many clusters this library finds in `text`: the work the benchmark times. -/
def oursClusterCount (text : String) : Nat :=
  (Segmentation.graphemes text).length

/-- How many clusters UnicodeExtra finds in `text`, without copying any of them. -/
def theirsClusterCount (text : String) : Nat := Id.run do
  let mut count := 0
  for _ in Unicode.graphemeClusters text do
    count := count + 1
  return count

end Bench
