import Bench.Measure

/-!
# The `bench-build-failure` executable

    lake exe bench-build-failure <failed target> <compiler output file> <output file>

Writes the results file that says the two libraries cannot build together. It imports neither
library, so it builds even when one of them does not. CI builds it before either library and
runs it when building this library, UnicodeExtra or the module that imports both fails. The run
metadata comes from the same environment variables as `bench report`.
-/

/-- How many of the compiler's last output lines the results file shows. -/
def errorTailLines : Nat := 40

def main (args : List String) : IO UInt32 := do
  match args with
  | [failedTarget, compilerOutputPath, outputPath] =>
    let run ← Bench.runMetaFromEnv
    let lines := (← IO.FS.readFile compilerOutputPath).splitOn "\n"
    let errorTail := "\n".intercalate (lines.drop (lines.length - errorTailLines))
    IO.FS.writeFile outputPath (Bench.renderBuildFailure run { failedTarget, errorTail })
    return 0
  | _ =>
    IO.eprintln "usage: bench-build-failure <failed target> <compiler output file> <output file>"
    return 2
