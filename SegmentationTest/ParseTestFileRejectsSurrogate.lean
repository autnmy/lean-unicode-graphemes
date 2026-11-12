import SegmentationTest.GraphemeBreakTestFile

-- "`lake test` passes all 853 lines of the test file."
-- D800 is not a valid Char; Char.ofNat would quietly turn it into U+0000, so
-- the parser must refuse the line instead of comparing a different text.
theorem «parseTestFile fails on a surrogate code point beside a valid line» :
    (SegmentationTest.GraphemeBreakTestFile.parseTestFile
      "÷ 0020 ÷ 0020 ÷\t# ok\n÷ D800 ÷\t# surrogate\n").toBool = false := by
  decide
