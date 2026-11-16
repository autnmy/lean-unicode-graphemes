import Bench.Compare
import Bench.Libraries
import Bench.Measure

/-!
# The `bench` executable

    lake exe bench check [--break-ours | --break-fast]   compare the three segmenters' clusters
    lake exe bench measure <library> <input>   one child measurement (spawned by `report`)
    lake exe bench report <output file>   measure every input and write the results table

`check` compares this library's reference segmenter, UnicodeExtra and this library's fast
segmenter on every input. It exits with status 1 and prints the first difference when they
disagree. `--break-ours` drops the last cluster of this library's reference output, and
`--break-fast` drops the last cluster of the fast output, so CI can show that a difference in
either list really fails `check`.
-/

namespace Bench

inductive Command where
  /-- Compare the three segmenters; `broken` names the one whose last cluster is dropped. -/
  | check (broken : Option Library)
  | measure (library : Library) (kind : InputKind)
  | report (outputPath : System.FilePath)

def usage : String :=
  "usage: bench check [--break-ours | --break-fast] | " ++
  "bench measure <baseline|ours|theirs|fast> <input> | bench report <output file>"

/-- The command named by `args`. Any other argument list, such as two break flags at once, is
`none`, so `main` prints the usage and exits 2 rather than running an unbroken check. -/
def parseCommand : List String → Option Command
  | ["check"] => some (.check none)
  | ["check", "--break-ours"] => some (.check (some .ours))
  | ["check", "--break-fast"] => some (.check (some .fast))
  | ["measure", library, kind] => do
    pure (.measure (← Library.ofName? library) (← InputKind.ofName? kind))
  | ["report", path] => some (.report path)
  | _ => none

/-- The cluster count a child process times for `library`; the baseline times nothing. -/
def clusterCountOf : Library → Option (String → Nat)
  | .baseline => none
  | .ours => some oursClusterCount
  | .theirs => some theirsClusterCount
  | .fast => some fastClusterCount

/-- The message `check` prints for `d`: the input and index, then one line per segmenter. -/
def describeDifference (d : Difference) : String :=
  -- `repr` quotes the cluster and escapes control characters such as CR and LF.
  let describeCluster : Option String → String
    | some cluster => (repr cluster).pretty
    | none => "(no cluster: the list has ended)"
  s!"The segmenters' clusters differ on input {d.input} at cluster {d.index}:\n" ++
  s!"  lean-unicode-graphemes: {describeCluster d.ours}\n" ++
  s!"  UnicodeExtra:           {describeCluster d.theirs}\n" ++
  s!"  fast (sliceGraphemes):  {describeCluster d.fast}"

/-- The clusters of `library`, with the last cluster dropped when `library` is `broken`. -/
def clustersFor (broken : Option Library) (library : Library) (clusters : String → List String) :
    String → List String :=
  if broken = some library then fun text => (clusters text).dropLast else clusters

/-- Compares the three segmenters on every input and returns the exit status. -/
def runCheck (broken : Option Library) : IO UInt32 := do
  let result := checkAll (clustersFor broken .ours oursClusters)
    (clustersFor broken .theirs theirsClusters) (clustersFor broken .fast fastClusters)
    (inputs fixedSeed)
  match result with
  | some d => IO.eprintln (describeDifference d)
  | none => IO.println "All three segmenters return the same clusters on every input."
  return exitCodeFor result

def runReport (outputPath : System.FilePath) : IO UInt32 := do
  let run ← runMetaFromEnv
  let rows ← InputKind.all.mapM measureRow
  let table := renderTable run rows
  IO.FS.writeFile outputPath table
  IO.println table
  return 0

end Bench

open Bench in
def main (args : List String) : IO UInt32 := do
  match parseCommand args with
  | some (.check broken) => runCheck broken
  | some (.measure library kind) =>
    measureChild (clusterCountOf library) kind
    return 0
  | some (.report path) => runReport path
  | none =>
    IO.eprintln usage
    return 2
