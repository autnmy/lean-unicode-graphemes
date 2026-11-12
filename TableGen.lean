import TableGen.Ucd
import TableGen.Render

/-!
# Table generator

Reads the Unicode Character Database files under `data/ucd/` and turns them
into the property tables the library looks code points up in. The library
itself does not import this code: the generator and the test driver do.
-/
