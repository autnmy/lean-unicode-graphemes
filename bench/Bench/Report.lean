/-!
# Benchmark statistics and the results table

The CI job uploads one markdown file: a table of the measurements and a list saying where they
were taken. Everything here is pure, so the tests can check what the file says without running
a benchmark. The file reports numbers only; it holds no sentence that judges which library is
faster.

When the two libraries cannot build together on the bench toolchain there are no numbers, and
the file states that result instead, with the target that failed and the compiler's last lines.
-/

namespace Bench

/-- The median, minimum, maximum and number of a list of timing samples. -/
structure Stats where
  median : Nat
  min : Nat
  max : Nat
  count : Nat
  deriving DecidableEq, Repr

/-- Inserts `x` into the ascending list `sorted`. Structural recursion keeps `summarize`
reducible by `decide`, which well-founded sorts are not. -/
private def insertAscending (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insertAscending x ys

private def sortAscending : List Nat → List Nat
  | [] => []
  | x :: xs => insertAscending x (sortAscending xs)

/-- Summarizes `samples`. For an even count the median is the lower of the two middle samples,
so it is always a value that was measured, never an average of two. An empty list gives zeros. -/
def summarize (samples : List Nat) : Stats :=
  let sorted := sortAscending samples
  let count := sorted.length
  { median := sorted.getD ((count - 1) / 2) 0,
    min := sorted.headD 0,
    max := sorted.getLastD 0,
    count }

/-- Where and on what the benchmark ran. -/
structure RunMeta where
  /-- The runner's machine description: CPU model, core count and `uname -a`. -/
  machine : String
  toolchain : String
  /-- Full commit id of this library. -/
  oursCommit : String
  /-- Full commit id of UnicodeExtra that the copy in `vendor/UnicodeExtra` was taken from. -/
  theirsCommit : String

/-- The measurements for one input. Times are nanoseconds per call; peaks are kibibytes. -/
structure ResultRow where
  input : String
  /-- How many calls each timed sample ran; a sample's time is divided by this. -/
  callsPerSample : Nat
  ours : Stats
  theirs : Stats
  baselinePeakKb : Nat
  oursPeakKb : Nat
  theirsPeakKb : Nat

/-- How memory is measured, stated in the results so a reader knows what the peaks include. -/
def memoryMethod : String :=
  "Peak memory is the peak resident set size (`VmHWM` in `/proc/self/status`) of a separate " ++
  "process per input and library. Each peak includes building the input. The baseline " ++
  "process only builds the input. Peaks are shown as measured, with nothing subtracted."

/-- How time is measured. -/
def timingMethod : String :=
  "Times are nanoseconds per call, from `IO.monoNanosNow`, over the stated number of samples " ++
  "after warm-up runs that are not counted. Each call's result is consumed, so it is computed."

private def tableHeader : List String :=
  [ "| Input | Samples | Calls per sample | This library median (ns) | This library min-max (ns) " ++
      "| UnicodeExtra median (ns) | UnicodeExtra min-max (ns) | Baseline peak (KiB) " ++
      "| This library peak (KiB) | UnicodeExtra peak (KiB) |",
    "|---|---|---|---|---|---|---|---|---|---|" ]

private def renderRow (row : ResultRow) : String :=
  let cells := [ row.input, toString row.ours.count, toString row.callsPerSample,
    toString row.ours.median, s!"{row.ours.min}-{row.ours.max}",
    toString row.theirs.median, s!"{row.theirs.min}-{row.theirs.max}",
    toString row.baselinePeakKb, toString row.oursPeakKb, toString row.theirsPeakKb ]
  "| " ++ " | ".intercalate cells ++ " |"

private def renderRunMeta (run : RunMeta) : List String :=
  [ s!"- Machine: {run.machine}",
    s!"- Toolchain: {run.toolchain}",
    s!"- lean-unicode-graphemes commit: {run.oursCommit}",
    s!"- UnicodeExtra commit: {run.theirsCommit}" ]

/-- The results file: one table of the measurements, then the run's metadata and methods. -/
def renderTable (run : RunMeta) (rows : List ResultRow) : String :=
  "\n".intercalate (
    ["# Benchmark results", ""] ++ tableHeader ++ rows.map renderRow ++
    [""] ++ renderRunMeta run ++
    [s!"- Timing: {timingMethod}", s!"- Memory: {memoryMethod}"]) ++ "\n"

/-- A library target that failed to build on the bench toolchain. -/
structure BuildFailure where
  /-- The target that failed: this library, UnicodeExtra, or the module importing both. -/
  failedTarget : String
  /-- The last lines of the compiler's output. -/
  errorTail : String

/-- The results file when the two libraries cannot build together: the failure, no numbers. -/
def renderBuildFailure (run : RunMeta) (failure : BuildFailure) : String :=
  "\n".intercalate (
    [ "# Benchmark results: the libraries cannot build together", "",
      s!"Building `{failure.failedTarget}` failed on {run.toolchain}, " ++
        "so nothing was measured.", "" ] ++
    renderRunMeta run ++
    -- A four-backtick fence, so a three-backtick line in the compiler output cannot close it.
    [ "", "Last lines of the compiler output:", "", "````", failure.errorTail, "````" ]) ++ "\n"

end Bench
