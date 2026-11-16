import Main

-- "`--break-ours` drops the last cluster of this library's list only, and `--break-fast` drops
-- the last cluster of the fast list only."
-- A `--break-fast` routed to this library's list, or parsed as an unbroken check, would let
-- `lake exe bench check --break-fast` prove nothing about the fast column (or exit 0).
/-- The --break-fast flag breaks the fast list, not this library's list and not nothing. -/
theorem parse_command_break_fast_breaks_only_fast_list :
    (match Bench.parseCommand ["check", "--break-fast"],
           Bench.parseCommand ["check", "--break-ours"] with
     | some (.check (some .fast)), some (.check (some .ours)) => true
     | _, _ => false) = true := by
  decide
