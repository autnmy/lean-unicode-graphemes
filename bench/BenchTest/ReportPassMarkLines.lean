import Bench.Report

-- "Each line shows the fast median next to UnicodeExtra's min and max and whether it passes, for
-- example `- plain-ascii: fast median 9000 ns, UnicodeExtra min-max 9254-10788 ns, fast median at
-- most UnicodeExtra max: yes`."
-- plain-ascii sits exactly at the mark and reads yes; emoji is one nanosecond above and reads no.
-- Each input's pass-mark line shows its own fast median, UnicodeExtra's min-max, and its own yes
-- or no.
#guard
    (let run : Bench.RunMeta :=
        { machine := "m", toolchain := "t", oursCommit := "o", theirsCommit := "u" }
      let row (input : String) (fastMedian : Nat) : Bench.ResultRow :=
        { input, callsPerSample := 7,
          ours := { median := 41, min := 40, max := 42, count := 3 },
          theirs := { median := 300, min := 200, max := 500, count := 3 },
          fast := { median := fastMedian, min := 11, max := 990, count := 3 },
          baselinePeakKb := 61, oursPeakKb := 62, theirsPeakKb := 63, fastPeakKb := 64 }
      let lines := (Bench.renderTable run [row "plain-ascii" 500, row "emoji" 501]).splitOn "\n"
      lines.contains ("- plain-ascii: fast median 500 ns, UnicodeExtra min-max 200-500 ns, " ++
          "fast median at most UnicodeExtra max: yes") &&
        lines.contains ("- emoji: fast median 501 ns, UnicodeExtra min-max 200-500 ns, " ++
          "fast median at most UnicodeExtra max: no"))
