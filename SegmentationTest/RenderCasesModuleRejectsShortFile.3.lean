import SegmentationTest.GraphemeBreakTestFile

-- "The repository has a theorem stating that `graphemes` matches every one of the 853 lines of
-- GraphemeBreakTest.txt". A truncated file whose trailer was edited to agree must never render
-- into the data the theorem reads.
theorem «renderCasesModule refuses a test file whose trailer agrees with a count other than 853 (R1)» :
    (match SegmentationTest.GraphemeBreakTestFile.renderCasesModule
        "UNICODE LICENSE V3\n\nCopyright © 1991-2025 Unicode, Inc.\n"
        "÷ 0020 ÷ 0020 ÷\t# x\n#\n# Lines: 1\n#\n# EOF\n" with
      | .error _ => true
      | .ok _ => false) = true := by
  decide +kernel
