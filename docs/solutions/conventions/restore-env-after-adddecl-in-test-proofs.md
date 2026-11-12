---
module: SegmentationTest
date: 2026-11-12
problem_type: convention
component: testing_framework
severity: high
audience: both
related_components:
  - Gate.Axioms
tags:
  - adddecl
  - run-tac
  - axioms
  - environment
  - test-isolation
applies_when:
  - A test adds declarations with addDecl inside run_tac or another metaprogram
  - A test adds an axiom, especially one of False, to check that a gate rejects it
---

# Restore the environment after `addDecl` in a test proof

## Context

`SegmentationTest/AssertAxiomsRejectsForeignAxiom.lean` checks that `#assert_axioms` rejects a theorem that depends on an axiom outside the allowed list. It cannot write `axiom` in source, because project code bans that word. So it uses `addDecl` inside `run_tac` to add an axiom of type `False`, plus a theorem that uses it.

Before the fix, the code did not remove the declarations when the proof ended. `addDecl` changes the environment of the module being elaborated, and Lean saves that environment in the compiled module. Every file that imports the test module then gets the axiom of `False`. Restoring the saved messages does not remove the declarations. A check that imported the built module confirmed that the axiom was exported.

## Solution

Save the environment before `addDecl`. Restore it with `setEnv` after the negative check:

```lean
let envBefore ← getEnv
addDecl (.axiomDecl { name := badAx, levelParams := [], type := mkConst ``False, isUnsafe := false })
...
modifyThe Core.State fun s => { s with messages := saved }
setEnv envBefore
```

Put the names under the current declaration name, which `Term.getDeclName?` returns. Lean requires this for declarations added inside a proof.

## Why it matters

A saved axiom of `False` in a test module can prove anything in any module that imports it. The axiom gate checks only the theorems it is given, so it never sees the leak. A comment that says the axiom exists "only while this proof runs" is a claim, not a check. To verify it, build the module, import it into a new file, and search the constants for the synthetic name.

## Evidence

- PR #23 adds `SegmentationTest/AssertAxiomsRejectsForeignAxiom.lean`. It saves `envBefore ← getEnv` before the two `addDecl` calls and calls `setEnv envBefore` after the rejection check. Its comment says the restore stops the axiom of `False` from being exported to importing modules.
- `SegmentationTest.lean` in PR #23 imports this test module, so `lake test` builds it alongside the other tests.
- Verification step to run: `lake build SegmentationTest.AssertAxiomsRejectsForeignAxiom`. Then elaborate a file that imports it and lists constants whose names end in `.GateAcceptance.foreignAxiom`. The list must be empty.
