import Bench.Report

-- "A `large-mixed` row with baseline 1000, fast 9000 and theirs 4000 shows 9000 and 4000, and
-- never 8000 or 3000."
-- "Report peaks raw, never subtracted from the input-only baseline."
-- The large-mixed peak line shows the fast and UnicodeExtra peaks as measured, and no peak minus
-- the baseline appears anywhere.
#guard
    (let run : Bench.RunMeta :=
        { machine := "m", toolchain := "t", oursCommit := "o", theirsCommit := "u" }
      let row : Bench.ResultRow :=
        { input := "large-mixed", callsPerSample := 1,
          ours := { median := 41, min := 40, max := 42, count := 7 },
          theirs := { median := 51, min := 50, max := 52, count := 7 },
          fast := { median := 71, min := 70, max := 72, count := 7 },
          baselinePeakKb := 1000, oursPeakKb := 2000, theirsPeakKb := 4000, fastPeakKb := 9000 }
      let text := Bench.renderTable run [row]
      (text.splitOn "\n").contains "- Peak memory on large-mixed: fast 9000 KiB, UnicodeExtra 4000 KiB" &&
        (text.splitOn "8000").length == 1 && (text.splitOn "3000").length == 1)
