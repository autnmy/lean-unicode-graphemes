import Bench.Report

-- The rendered table has the fast median, fast min-max and fast peak columns in its header, and
-- the row shows the fast figures after UnicodeExtra's timings with the fast peak last.
#guard
    (let run : Bench.RunMeta :=
        { machine := "test machine", toolchain := "test toolchain",
          oursCommit := "ours", theirsCommit := "theirs" }
     let row : Bench.ResultRow :=
        { input := "plain-ascii", callsPerSample := 100,
          ours := { median := 200, min := 100, max := 300, count := 3 },
          theirs := { median := 20, min := 10, max := 30, count := 3 },
          fast := { median := 70, min := 60, max := 80, count := 3 },
          baselinePeakKb := 1111, oursPeakKb := 2222, theirsPeakKb := 3333,
          fastPeakKb := 4444 }
     let text := Bench.renderTable run [row]
     let mentions (part : String) : Bool := (text.splitOn part).length > 1
     mentions "Fast median (ns)" && mentions "Fast min-max (ns)" &&
       mentions "Fast peak (KiB)" &&
       mentions "| plain-ascii | 3 | 100 | 200 | 100-300 | 20 | 10-30 | 70 | 60-80 | 1111 | 2222 | 3333 | 4444 |")
