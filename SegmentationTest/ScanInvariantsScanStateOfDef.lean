import Segmentation

open Segmentation

-- "Define `def Segmentation.scanStateOf (p : Props) (ps : List Props) : ScanState`, the state after reading `p :: ps` (`ps.foldl ScanState.push (ScanState.start p)`)."
theorem «scanStateOf is the fold of push from start» :
    ∀ (p : Props) (ps : List Props),
      Segmentation.scanStateOf p ps = ps.foldl ScanState.push (ScanState.start p) :=
  fun _ _ => rfl
