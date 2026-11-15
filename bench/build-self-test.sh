#!/bin/sh
# A build script that has only ever passed could be calling every failure the same thing. This
# runs build.sh against a stand-in `lake` that fails one build target at a time, and fails
# unless a library target writes the "cannot build together" results file and a benchmark
# target writes none. Both cases must exit non-zero. Run it from `bench/`; it needs no network.
set -eu

here=$(cd "$(dirname "$0")" && pwd)
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

# The stand-in `lake`: `lake build <target>` fails when <target> is $FAIL_TARGET, and
# `lake exe bench-build-failure <what> <log> <results>` writes the results file.
mkdir "$work/bin"
cat > "$work/bin/lake" <<'EOF'
#!/bin/sh
case "$1" in
  build)
    [ "$2" != "${FAIL_TARGET:-}" ] || { echo "stand-in failure building $2"; exit 1; } ;;
  exe)
    echo "cannot build together: $2" > "$5" ;;
esac
EOF
chmod +x "$work/bin/lake"

failures=0

# $1: the target that fails ("" for none), $2: expected exit (0 or nonzero),
# $3: whether a results file is expected (yes or no).
expect() {
  results="$work/results.md"
  rm -f "$results"
  if FAIL_TARGET=$1 PATH="$work/bin:$PATH" sh "$here/build.sh" "$results" > "$work/out" 2>&1
  then status=0; else status=1; fi
  written=no
  [ ! -e "$results" ] || written=yes
  wanted_status=0
  [ "$2" = 0 ] || wanted_status=1
  if [ "$status" -ne "$wanted_status" ] || [ "$written" != "$3" ]; then
    echo "FAIL target '$1': exit failed=$status (want $wanted_status), results file $written (want $3)" >&2
    cat "$work/out" >&2
    failures=$((failures + 1))
  else
    echo "PASS target '$1'"
  fi
}

expect "" 0 no
for target in +Segmentation +UnicodeExtra +Bench.Together; do
  expect "$target" nonzero yes
done
for target in bench-build-failure Bench bench bench-tests; do
  expect "$target" nonzero no
done

[ "$failures" -eq 0 ]
