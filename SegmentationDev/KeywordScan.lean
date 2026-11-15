import SegmentationDev.Gate.KeywordScan

/-!
# `lake exe keyword-scan <paths>`

Checks each named Lean file for the words `SegmentationDev.Gate.forbiddenWords` lists, used as
code, and prints each one as `path:line: word`. It exits with status 1 when it finds one, when a
file cannot be read, or when it is given no paths at all: a scan of nothing would otherwise pass.
CI passes it every tracked `.lean` file. The work is done by `SegmentationDev.Gate.scanFiles`.
-/

def main (args : List String) : IO UInt32 :=
  SegmentationDev.Gate.scanFiles args
