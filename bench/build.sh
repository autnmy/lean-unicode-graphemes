#!/bin/sh
# Builds the benchmark in stages, so a failure says whose code failed. A failure building this
# library, UnicodeExtra, or the module that only imports both (`Bench.Together`) is a fact about
# the two libraries on the bench toolchain: it is written to the results file and the script
# fails. A failure in any other step is the benchmark's own code, a harness failure, and writes
# no results file, because it says nothing about the libraries.
#
# Run it from `bench/` after `lake update`, with the BENCH_* variables `bench report` reads set.
# $1: the results file to write when the libraries cannot build together.
set -eu

results=$1
log=$(mktemp)
trap 'rm -f "$log"' EXIT

# $1: what to call the target in messages, $2: the `lake build` target.
build_harness() {
  echo "Building $1"
  if ! lake build "$2"; then
    echo "Harness build failed: the benchmark's own code ($1) does not compile." >&2
    exit 1
  fi
}

build_library() {
  echo "Building $1"
  if ! lake build "$2" > "$log" 2>&1; then
    cat "$log" >&2
    lake exe bench-build-failure "$1" "$log" "$results"
    echo "The libraries cannot build together: building $1 failed. See $results." >&2
    exit 1
  fi
  cat "$log"
}

# The failure reporter imports neither library, so it is built first and can still report
# when one of them fails.
build_harness "the build-failure reporter" bench-build-failure
build_library "lean-unicode-graphemes (Segmentation)" +Segmentation
build_library "UnicodeExtra" +UnicodeExtra
build_library "Bench.Together (both libraries imported together)" +Bench.Together
build_harness "the benchmark library" Bench
build_harness "the bench executable" bench
build_harness "the bench tests" bench-tests
echo "Both libraries and the benchmark built."
