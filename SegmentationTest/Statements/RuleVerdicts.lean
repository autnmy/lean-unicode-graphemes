import Segmentation

/-- `true` for a rule that puts a boundary (÷), `false` for one that forbids it (×). -/
def statementsRuleBreaks (r : Segmentation.Rule) : Bool :=
  match r.verdict with
  | .brk => true
  | .noBrk => false

-- UAX #29 revision 49 marks GB1, GB2, GB4, GB5 and GB999 with ÷ and every other rule with ×.
theorem «rules verdicts break only at GB1 GB2 GB4 GB5 and GB999» :
    Segmentation.rules.map statementsRuleBreaks =
      [true, true, false, true, true, false, false, false, false, false, false,
       false, false, false, false, true] := rfl
