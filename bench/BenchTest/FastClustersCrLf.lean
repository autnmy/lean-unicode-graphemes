import Bench.Libraries

-- "Name them `Bench.fastClusters (text : String) : List String` (it maps `String.Slice.copy` over the
-- slices) and `Bench.fastClusterCount (text : String) : Nat` (it takes `.length`)."
-- The fast clusters keep CR LF together and agree with the reference, and the fast count matches.
#guard
    (Bench.fastClusters "a\r\nb" == ["a", "\r\n", "b"] &&
      Bench.fastClusters "a\r\nb" == Bench.oursClusters "a\r\nb" &&
      Bench.fastClusterCount "a\r\nb" == 3)
