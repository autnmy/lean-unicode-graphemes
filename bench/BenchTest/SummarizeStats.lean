import Bench.Report

-- "times both (median and spread over enough repetitions to be stable)"
theorem «summarize gives median, min, max and count of unsorted samples» :
    (let s := Bench.summarize [5, 1, 3]
     s.median == 3 && s.min == 1 && s.max == 5 && s.count == 3) = true := by
  decide
