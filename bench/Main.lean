import Bench.Compare
import Bench.Libraries
import Bench.Measure

/-!
# The `bench` executable

    lake exe bench check [--break-ours]   compare both libraries' clusters on every input
    lake exe bench measure <library> <input>   one child measurement (spawned by `report`)
    lake exe bench report <output file>   measure every input and write the results table

`check` exits with status 1 and prints the first difference when the libraries disagree.
`--break-ours` drops the last cluster of this library's output, so CI can show that a
difference really fails `check`.
-/

namespace Bench

inductive Command where
  | check (breakOurs : Bool)
  | measure (library : Library) (kind : InputKind)
  | report (outputPath : System.FilePath)

def usage : String :=
  "usage: bench check [--break-ours] | bench measure <baseline|ours|theirs> <input> | " ++
  "bench report <output file>"

def parseCommand : List String → Option Command
  | ["check"] => some (.check false)
  | ["check", "--break-ours"] => some (.check true)
  | ["measure", library, kind] => do
    pure (.measure (← Library.ofName? library) (← InputKind.ofName? kind))
  | ["report", path] => some (.report path)
  | _ => none

/-- The cluster count a child process times for `library`; the baseline times nothing. -/
def clusterCountOf : Library → Option (String → Nat)
  | .baseline => none
  | .ours => some oursClusterCount
  | .theirs => some theirsClusterCount

def describeDifference (d : Difference) : String :=
  -- `repr` quotes the cluster and escapes control characters such as CR and LF.
  let describeCluster : Option String → String
    | some cluster => (repr cluster).pretty
    | none => "(no cluster: the list has ended)"
  s!"The libraries' clusters differ on input {d.input} at cluster {d.index}:\n" ++
  s!"  lean-unicode-graphemes: {describeCluster d.ours}\n" ++
  s!"  UnicodeExtra:           {describeCluster d.theirs}"

def runCheck (breakOurs : Bool) : IO UInt32 := do
  let ours := if breakOurs then fun text => (oursClusters text).dropLast else oursClusters
  let result := checkAll ours theirsClusters (inputs fixedSeed)
  match result with
  | some d => IO.eprintln (describeDifference d)
  | none => IO.println "Both libraries return the same clusters on every input."
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
  | some (.check breakOurs) => runCheck breakOurs
  | some (.measure library kind) =>
    measureChild (clusterCountOf library) kind
    return 0
  | some (.report path) => runReport path
  | none =>
    IO.eprintln usage
    return 2
