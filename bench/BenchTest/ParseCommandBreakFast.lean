import Main

-- "`--break-ours` drops the last cluster of this library's list only, and `--break-fast` drops the
-- last cluster of the fast list only."
/-- The break-fast flag parses to a check that breaks the fast list, and the break-ours flag still breaks this library's list. -/
theorem parseCommand_break_fast_breaks_fast_only :
    ((match Bench.parseCommand ["check", "--break-fast"] with
      | some (.check (some .fast)) => true
      | _ => false) &&
     (match Bench.parseCommand ["check", "--break-ours"] with
      | some (.check (some .ours)) => true
      | _ => false) &&
     (match Bench.parseCommand ["check"] with
      | some (.check none) => true
      | _ => false)) = true := by
  decide
