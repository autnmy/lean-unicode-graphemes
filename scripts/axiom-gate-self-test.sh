#!/bin/sh
# Shows that `#assert_axioms` (SegmentationDev/Gate/Axioms.lean) really fails. A gate that has only
# ever passed on a clean tree could be checking nothing, so this writes throwaway Lean files that
# each depend on a forbidden axiom and expects the gate to reject every one of them, naming the
# axiom. The files live in a temporary directory, never in the repository, because project code may
# not use these forms at all. Run it from the repository root after
# `lake build SegmentationGate Segmentation`.
set -eu

dir=$(mktemp -d)
trap 'rm -rf "$dir"' EXIT
failures=0

# $1: case name, $2: Lean source after the import line, $3: text the gate's error must contain.
expect_rejected() {
  file="$dir/$1.lean"
  printf 'import SegmentationDev.Gate.Axioms\n\n%s\n' "$2" > "$file"
  if output=$(lake env lean "$file" 2>&1); then
    echo "FAIL $1: the gate accepted it" >&2
    failures=$((failures + 1))
  elif printf '%s\n' "$output" | grep -q "depends on the disallowed axioms.*$3"; then
    echo "PASS $1: rejected"
  else
    echo "FAIL $1: it failed, but not with the gate's error naming $3:" >&2
    printf '%s\n' "$output" >&2
    failures=$((failures + 1))
  fi
}

# A control: without it, a broken import or toolchain would make every case above fail for the
# wrong reason and this script would still report success.
expect_accepted() {
  file="$dir/$1.lean"
  printf 'import SegmentationDev.Gate.Axioms\n\n%s\n' "$2" > "$file"
  if output=$(lake env lean "$file" 2>&1); then
    echo "PASS $1: accepted"
  else
    echo "FAIL $1: the gate rejected a proof that uses no forbidden axiom:" >&2
    printf '%s\n' "$output" >&2
    failures=$((failures + 1))
  fi
}

expect_accepted clean 'theorem clean : 1 + 1 = 2 := rfl
#assert_axioms clean'

expect_rejected sorry 'theorem usesSorry : 1 + 1 = 3 := by sorry
#assert_axioms usesSorry' 'sorryAx'

# On this toolchain `native_decide` adds an axiom of its own whose name contains
# `native_decide`, rather than depending on `Lean.ofReduceBool`.
expect_rejected native_decide 'theorem usesNativeDecide : 10 < 20 := by native_decide
#assert_axioms usesNativeDecide' 'native_decide'

expect_rejected user_axiom 'axiom selfTestAxiom : 1 + 1 = 3
theorem usesUserAxiom : 1 + 1 = 3 := selfTestAxiom
#assert_axioms usesUserAxiom' 'selfTestAxiom'

if [ "$failures" -ne 0 ]; then
  echo "$failures axiom gate self-test case(s) failed" >&2
  exit 1
fi
echo "axiom gate self-test passed"
