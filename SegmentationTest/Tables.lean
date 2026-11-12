import TableGen

/-!
# Table rendering checks

Compile-time checks of the pieces `TableGen.renderAll` builds the generated
modules from. The values the generated tables give for single code points are
checked by the `Props…` and `GcbOf…` test modules.
-/

namespace SegmentationTest.TableRenderChecks

def isError {α : Type} : Except String α → Bool
  | .error _ => true
  | .ok _ => false

def okValue? {α : Type} : Except String α → Option α
  | .ok value => some value
  | .error _ => none

-- Code points are written as the UCD files write them: upper case, at least four digits.
#guard TableGen.hex 0x41 == "0x0041"
#guard TableGen.hex 0x1F1E6 == "0x1F1E6"
#guard TableGen.hex 0x10FFFF == "0x10FFFF"

-- Chunks keep every element, in order, and none is longer than the limit.
#guard TableGen.chunks 2 [1, 2, 3, 4, 5] == [[1, 2], [3, 4], [5]]
#guard TableGen.chunks 2 ([] : List Nat) == []

-- The licence goes into one block comment, verbatim.
#guard okValue? (TableGen.licenceHeader "UNICODE LICENSE V3\n") == some "/-\nUNICODE LICENSE V3\n-/\n"
#guard okValue? (TableGen.licenceHeader "UNICODE LICENSE V3") == some "/-\nUNICODE LICENSE V3\n-/\n"
-- Lean block comments nest, so an opening `/-` would also move where the comment ends.
#guard isError (TableGen.licenceHeader "a /- b")
#guard isError (TableGen.licenceHeader "a -/ b")

end SegmentationTest.TableRenderChecks
