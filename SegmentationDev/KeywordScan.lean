import SegmentationDev.Gate.KeywordScan

/-!
# `lake exe keyword-scan <paths>`

Checks each named Lean file for the words `SegmentationDev.Gate.forbiddenWords` lists, used as
code, and prints each one as `path:line: word`. It exits with status 1 when it finds one, when a
file cannot be read, or when it is given no paths at all: a scan of nothing would otherwise pass.
CI passes it every tracked `.lean` file.
-/

def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    IO.eprintln "keyword-scan: no files given; pass the .lean files to check"
    return 1
  let mut problems := 0
  for path in args do
    try
      for (line, word) in SegmentationDev.Gate.findForbidden (← IO.FS.readFile path) do
        IO.eprintln s!"{path}:{line}: {word}"
        problems := problems + 1
    catch error =>
      IO.eprintln s!"keyword-scan: cannot read {path}: {error}"
      problems := problems + 1
  if problems == 0 then
    IO.println s!"keyword-scan: {args.length} files checked, no forbidden words"
    return 0
  else
    IO.eprintln s!"keyword-scan: {problems} problems in {args.length} files"
    return 1
