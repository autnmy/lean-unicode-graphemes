import TableGen

-- Dropping DerivedCoreProperties.txt from the list would leave that file unchecked
-- while the digest check still passes, so a short list must fail.
-- `decide` decodes the string literal while elaborating, one nested step per
-- character, which needs more than the default recursion depth.
set_option maxRecDepth 20000 in
theorem «checkDigestList rejects a SHA256SUMS that lists only four of the five files» :
    (TableGen.checkDigestList
      ("0839dcb79e4ac639ecd538b1abf7c9d22e3f9dd265b7e182d33627aa4d75b45a  auxiliary/GraphemeBreakProperty.txt\n" ++
       "b0cf047ee94485bbdc846de2b902f5f8a815f6b674f9d04223cddadd91c9df31  auxiliary/GraphemeBreakTest.txt\n" ++
       "80d00f8e616a0ef27fd6b8de3b758c06383b5d917e2977709578e68baf733bf1  emoji/emoji-data.txt\n" ++
       "e7a93b009565cfce55919a381437ac4db883e9da2126fa28b91d12732bc53d96  LICENSE.txt\n")
      matches .error _) = true := by
  decide
