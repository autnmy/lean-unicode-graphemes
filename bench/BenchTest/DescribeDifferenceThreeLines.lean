import Main

-- "`describeDifference` prints three labelled lines, and its first line keeps the words "clusters
-- differ on input"."
-- The difference message names the input on its first line with the words clusters differ on
-- input, then shows one line per segmenter. A `#guard`, because the kernel cannot reduce
-- `String.splitOn`.
#guard
  let lines := (Bench.describeDifference
    { input := "emoji", index := 2, ours := some "a", theirs := some "a", fast := none }
    ).splitOn "\n"
  lines.length == 4 &&
    ((lines.headD "").splitOn "clusters differ on input").length > 1 &&
    ((lines.headD "").splitOn "emoji").length > 1 &&
    ((lines.getD 3 "").splitOn "(no cluster: the list has ended)").length > 1
