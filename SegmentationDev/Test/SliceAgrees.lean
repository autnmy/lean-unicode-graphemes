import Lean
import Segmentation
import SegmentationDev.Test.SliceAgreesTypePin
import SegmentationDev.Test.SliceAsciiPropsTypePin
import SegmentationDev.Test.SliceCharProps
import SegmentationDev.Test.CharPropsLookups
import SegmentationDev.Test.SliceAgreesEdgeInputs
import SegmentationDev.Test.SliceAgreesSubSlice
import SegmentationDev.Test.SliceClustersMatchCuts
import SegmentationDev.Test.SliceScannerNoCopy
import SegmentationDev.Test.SliceAgreeHeadlineGate
import SegmentationDev.Test.SliceFastNoReference

/-!
# The `String.Slice` scanner agrees with the reference

`Segmentation.sliceGraphemes_agree` proves the scanner equal to `graphemes` and `boundaries` on
`s.toSlice` for every `String s`. The modules imported here check the rest by running it:

* the type of `sliceGraphemes_agree`, both halves spelled out, and of `asciiProps_eq_props`;
* compiled `#guard` checks against the reference `clustersOf` and mapped `cutsOf` on the edge
  inputs of the ASCII path, which the `@[csimp]` rewrite of `graphemes` and `boundaries` leaves
  on the `List Char` code, with expected byte cuts computed only from the reference;
* a sub-slice from the middle of a larger string, which `sliceGraphemes_agree_clustersOf` proves
  for any slice and these checks run: its clusters are slices of the sub-slice, its cuts are
  measured from the sub-slice start, and a CR at its end is not joined with the LF just past it;
* that each cluster's byte bounds are neighbouring cuts, that the clusters are views of the
  input rather than copies, and that the empty input has one cut at 0;
* that `sliceGraphemes_agree` and the four statements proved for `graphemesFast` and
  `boundariesFast` pass the axiom gate and are in both headline lists;
* that `graphemesFast` and `boundariesFast` are computed from `sliceGraphemes` and reach neither
  `graphemes`, `boundaries`, `clustersOf` nor `cutsOf`, so what runs after the csimp rewrite is
  the scanner.

Each module holds one concern, so a failure names the behaviour it checks. The check below
makes sure every definition on the scanner's path, the internal scan included, is plain with no
compiled substitute, so the proof covers the code that runs.
-/

-- "No `partial def` anywhere in the proved path: a `partial def` has no equation lemmas, so the
-- proof cannot unfold it."
-- A `partial` definition is stored as an opaque constant and a compiler substitute is recorded as
-- an attribute, so neither shows up as an axiom; the keyword scan does not look for `partial`.
open Lean in
theorem slice_scanner_definitions_are_plain_with_no_compiled_substitute : True := by
  run_tac do
    let env ← getEnv
    for name in [``Segmentation.sliceGraphemes, ``Segmentation.sliceBoundaries,
        ``Segmentation.charProps, ``Segmentation.asciiProps, ``Segmentation.scanClusters,
        ``Segmentation.clusterBounds, ``Segmentation.graphemesFast,
        ``Segmentation.boundariesFast, ``Segmentation.breaksBeforeFast] do
      match env.find? name with
      | some (.defnInfo _) => pure ()
      | some _ => throwError m!"{name} is not a plain definition (a partial definition is opaque)"
      | none => throwError m!"{name} is missing"
      if (Compiler.getImplementedBy? env name).isSome then
        throwError m!"{name} has a compiled substitute the proof does not cover"
      if isExtern env name then
        throwError m!"{name} is bound to foreign code the proof does not cover"
  trivial
