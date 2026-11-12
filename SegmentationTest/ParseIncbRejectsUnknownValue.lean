import TableGen

-- Only Consonant, Extend and Linker are InCB values the type can hold.
-- Any other value on an InCB line must stop the parse.
theorem «parseIncb rejects an unknown InCB value instead of defaulting to None» :
    (TableGen.parseIncb "094D ; InCB; Linkr # misspelled\n" matches .error _) = true := by
  decide
