import TableGen

-- The issue says: "Check the files against `SHA256SUMS` in `lake test` and in CI; do not download or replace them."
-- A SHA256SUMS list that swaps one expected file for another path, here one that
-- climbs out of the data directory, must fail rather than check a different file.
-- `decide` decodes the string literal while elaborating, one nested step per
-- character, which needs more than the default recursion depth.
set_option maxRecDepth 20000 in
theorem «checkDigestList rejects a SHA256SUMS entry naming a path outside the five expected files» :
    (TableGen.checkDigestList
      ("0839dcb79e4ac639ecd538b1abf7c9d22e3f9dd265b7e182d33627aa4d75b45a  auxiliary/GraphemeBreakProperty.txt\n" ++
       "b0cf047ee94485bbdc846de2b902f5f8a815f6b674f9d04223cddadd91c9df31  auxiliary/GraphemeBreakTest.txt\n" ++
       "80d00f8e616a0ef27fd6b8de3b758c06383b5d917e2977709578e68baf733bf1  emoji/emoji-data.txt\n" ++
       "09c928886a178fcafd93c29e4bd59073a058e5a100b716d425cb563ab50f68c9  ../../../README.md\n" ++
       "e7a93b009565cfce55919a381437ac4db883e9da2126fa28b91d12732bc53d96  LICENSE.txt\n")
      matches .error _) = true := by
  decide
