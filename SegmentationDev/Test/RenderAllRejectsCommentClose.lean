import SegmentationDev.TableGen

-- The licence is copied verbatim into a Lean block comment. A `-/` inside it
-- would end that comment early and turn the rest of the text into Lean code in
-- the generated module, so the generator must refuse it.
theorem renderAll_refuses_licence_closing_header_comment :
    (SegmentationDev.TableGen.renderAll
      "UNICODE LICENSE V3 -/ def injected : Nat := 0"
      "0041 ; Control # x\n"
      "00A9 ; Extended_Pictographic# x\n"
      "094D ; InCB; Linker # x\n"
      matches .error _) = true := by
  decide
