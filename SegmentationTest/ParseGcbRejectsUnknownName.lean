import TableGen

-- A misspelled value must be an error. Falling back to `Other` would give the
-- code point the default value in the tables and in the check that reads the
-- same parse, so neither would notice.
theorem «parseGcb rejects an unknown Grapheme_Cluster_Break value name instead of defaulting to Other» :
    (TableGen.parseGcb "1F1E6 ; Regional_Indicatr # misspelled\n" matches .error _) = true := by
  decide
