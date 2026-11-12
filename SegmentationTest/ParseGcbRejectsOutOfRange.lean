import TableGen

-- A line naming a value past the last Unicode code point is malformed data.
-- It must stop the parse with an error, never be kept or clamped.
theorem «parseGcb rejects a code point above U+10FFFF instead of storing it» :
    (TableGen.parseGcb "110000 ; Control # out of range\n" matches .error _) = true := by
  decide
