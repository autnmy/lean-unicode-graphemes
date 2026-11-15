import Lean
import Segmentation
import SegmentationDev.Test.SliceAgreesTypePin
import SegmentationDev.Test.SliceAsciiPropsTypePin
import SegmentationDev.Test.SliceCharProps
import SegmentationDev.Test.CharPropsLookups
import SegmentationDev.Test.SliceDefinitionsArePlain
import SegmentationDev.Test.SliceAgreesEdgeInputs
import SegmentationDev.Test.SliceAgreesSubSlice
import SegmentationDev.Test.SliceSubSliceStopsAtItsEnd
import SegmentationDev.Test.SliceClustersMatchCuts
import SegmentationDev.Test.SliceScannerNoCopy
import SegmentationDev.Test.SliceEmptyInputHasOneCut
import SegmentationDev.Test.SliceMultiByteCutsAreBytes
import SegmentationDev.Test.SliceAsciiRunJoinsFollowingExtender
import SegmentationDev.Test.SliceAsciiRunResetsScanState
import SegmentationDev.Test.SliceAgreeHeadlineGate

/-!
# The `String.Slice` scanner agrees with the reference

`Segmentation.sliceGraphemes_agree` proves the scanner equal to `graphemes` and `boundaries` on
`s.toSlice` for every `String s`. The modules imported here check the rest by running it:

* the type of `sliceGraphemes_agree`, both halves spelled out, and of `asciiProps_eq_props`;
* that the scanner's definitions are plain, with no compiled substitute, so the proof covers the
  code that runs;
* compiled `#guard` checks against `graphemes` and mapped `boundaries` on the edge inputs of the
  ASCII path, with expected byte cuts computed only from the reference;
* a sub-slice from the middle of a larger string, which the theorem does not cover: its clusters
  are slices of the sub-slice, its cuts are measured from the sub-slice start, and a CR at its end
  is not joined with the LF just past it;
* that each cluster's byte bounds are neighbouring cuts, that the clusters are views of the
  input rather than copies, and that the empty input has one cut at 0;
* that `sliceGraphemes_agree` passes the axiom gate and is in both headline lists.

Each check lives in its own module so a failure names the behaviour it checks. The one check
below extends the plain-definition check to the internal scan the two entry points share.
-/

-- "No `partial def` anywhere in the proved path." The entry points are checked in
-- `SegmentationDev/Test/SliceDefinitionsArePlain.lean`; the scan they both call must be plain too,
-- or the proof would be about a definition the compiled code does not run.
open Lean in
theorem slice_internal_scan_definitions_are_plain_with_no_compiled_substitute : True := by
  run_tac do
    let env ← getEnv
    for name in [``Segmentation.scanClusters, ``Segmentation.clusterBounds] do
      match env.find? name with
      | some (.defnInfo _) => pure ()
      | some _ => throwError m!"{name} is not a plain definition (a partial definition is opaque)"
      | none => throwError m!"{name} is missing"
      if (Compiler.getImplementedBy? env name).isSome then
        throwError m!"{name} has a compiled substitute the proof does not cover"
      if isExtern env name then
        throwError m!"{name} is bound to foreign code the proof does not cover"
  trivial
