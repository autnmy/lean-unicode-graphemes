import Segmentation
import TableGen

-- Check the files against `SHA256SUMS` in `lake test` and in CI; do not download or replace them.
-- With LICENSE.txt dropped from the list, `sha256sum --check` would pass on the four left,
-- so the list itself must be rejected.
-- `decide` decodes the string literal while elaborating, one nested step per
-- character, which needs more than the default recursion depth.
set_option maxRecDepth 20000 in
theorem «R1 checkDigestList fails when SHA256SUMS lists only four of the five files» :
    (match TableGen.checkDigestList
        "0839dcb79e4ac639ecd538b1abf7c9d22e3f9dd265b7e182d33627aa4d75b45a  auxiliary/GraphemeBreakProperty.txt\nb0cf047ee94485bbdc846de2b902f5f8a815f6b674f9d04223cddadd91c9df31  auxiliary/GraphemeBreakTest.txt\n80d00f8e616a0ef27fd6b8de3b758c06383b5d917e2977709578e68baf733bf1  emoji/emoji-data.txt\n09c928886a178fcafd93c29e4bd59073a058e5a100b716d425cb563ab50f68c9  DerivedCoreProperties.txt\n" with
     | .error _ => true
     | .ok _ => false) = true := by decide
