import Main

-- The plan's choice: an argument list naming two broken lists, or an unknown break flag, is not a
-- command, so it never runs as an unbroken check that exits 0.
/-- Both break flags together, a repeated flag, or an unknown break flag do not parse as a command. -/
theorem parseCommand_rejects_two_break_flags :
    ((Bench.parseCommand ["check", "--break-ours", "--break-fast"]).isNone &&
      (Bench.parseCommand ["check", "--break-fast", "--break-fast"]).isNone &&
      (Bench.parseCommand ["check", "--break-theirs"]).isNone) = true := by
  decide
