import Bench.Report

-- "The table keeps one `|---` line and never uses the words "faster" or "slower", because existing
-- guards in `bench/BenchTest/ReportRendering.lean` check both."
-- With fast columns and pass-mark lines rendered, the report has exactly one table rule line and
-- never says faster or slower.
#guard
    (let run : Bench.RunMeta :=
        { machine := "m", toolchain := "t", oursCommit := "o", theirsCommit := "u" }
      let row (input : String) (fastMedian : Nat) : Bench.ResultRow :=
        { input, callsPerSample := 7,
          ours := { median := 41, min := 40, max := 42, count := 3 },
          theirs := { median := 300, min := 200, max := 500, count := 3 },
          fast := { median := fastMedian, min := 11, max := 990, count := 3 },
          baselinePeakKb := 61, oursPeakKb := 62, theirsPeakKb := 63, fastPeakKb := 64 }
      let text := Bench.renderTable run [row "plain-ascii" 500, row "large-mixed" 501]
      ((text.splitOn "\n").filter (·.startsWith "|---")).length == 1 &&
        (text.splitOn "faster").length == 1 && (text.splitOn "slower").length == 1 &&
        (text.splitOn "Pass mark").length > 1)
