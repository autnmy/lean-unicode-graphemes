import Main

-- `Command.check` holds one broken library, so an argument list with two flags, a repeated
-- flag or an unknown flag must not parse; parsing it as an unbroken check would exit 0 on a typo.
/-- Two break flags, a repeated flag and an unknown break flag are all rejected by the parser. -/
theorem parse_command_rejects_combined_or_unknown_break_flags :
    ((Bench.parseCommand ["check", "--break-ours", "--break-fast"]).isNone &&
      (Bench.parseCommand ["check", "--break-fast", "--break-fast"]).isNone &&
      (Bench.parseCommand ["check", "--break-theirs"]).isNone &&
      (Bench.parseCommand ["check", "--break-fast"]).isSome) = true := by
  decide
