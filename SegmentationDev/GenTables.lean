import SegmentationDev.TableGen
import SegmentationDev.Test.GraphemeBreakTestFile

/-!
# `lake exe gen-tables`

Reads the UCD files under `data/ucd/<version>/` and writes the generated table
modules under `Segmentation/Tables/`, and the cases of `GraphemeBreakTest.txt`
to `SegmentationDev/Test/GraphemeBreakTestData.lean`. Run it from the package root.
Any input file that cannot be read or parsed stops it with exit status 1 before
it writes anything, so bad input never leaves a default-filled table. The
modules are written one at a time, so a failed write can leave some updated and
others not; the drift check in `lake test` and CI then reports the mismatch.
-/

open SegmentationDev.TableGen SegmentationDev.Test.GraphemeBreakTestFile in
def main : IO UInt32 := do
  try
    let read (file : String) : IO String := IO.FS.readFile (dataDir / file)
    let licence ← read "LICENSE.txt"
    let gcbText ← read "auxiliary/GraphemeBreakProperty.txt"
    let extPictText ← read "emoji/emoji-data.txt"
    let incbText ← read "DerivedCoreProperties.txt"
    let testText ← read "auxiliary/GraphemeBreakTest.txt"
    let rendered : Except String (List (System.FilePath × String)) := do
      let tables ← renderAll licence gcbText extPictText incbText
      let cases ← renderCasesModule licence testText
      pure (tables ++ [(casesModulePath, cases)])
    match rendered with
    | .error message =>
      IO.eprintln s!"gen-tables: {message}"
      return 1
    | .ok modules =>
      for (path, contents) in modules do
        IO.FS.writeFile path contents
        IO.println s!"wrote {path}"
      return 0
  catch e =>
    IO.eprintln s!"gen-tables: {e}"
    return 1
