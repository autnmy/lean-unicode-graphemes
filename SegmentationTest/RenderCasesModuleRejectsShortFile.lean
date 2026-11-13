import SegmentationTest.GraphemeBreakTestFile

-- A truncated file must never render, or the theorem would be proved over fewer than 853 lines.
theorem «renderCasesModule refuses a file with fewer test lines than its trailer states» :
    (SegmentationTest.GraphemeBreakTestFile.renderCasesModule
      "UNICODE LICENSE V3\n"
      "÷ 0020 ÷ 0020 ÷\t# x\n÷ 0020 × 0308 ÷\t# y\n#\n# Lines: 853\n#\n# EOF\n").toBool = false := by
  decide +kernel
