# lean-unicode-graphemes
Unicode text segmentation (UAX #29) for Lean 4, with machine-checked proofs

The `Segmentation` library splits text into extended grapheme clusters: the
user-perceived characters that cursor movement, deletion and truncation should
treat as one unit. It follows Unicode 18.0.0 and
[UAX #29 revision 49](https://www.unicode.org/reports/tr29/tr29-49.html)
(`Segmentation/Version.lean` holds both versions), and uses Lean core only,
with no Mathlib, Batteries or other Lake dependencies.

For speed, call the slice scanner in `Segmentation/Slice.lean`:

- `Segmentation.sliceGraphemes : String.Slice → List String.Slice` splits
  text into extended grapheme clusters, each one a slice of the input, so
  nothing is copied.
- `Segmentation.sliceBoundaries (s : String.Slice) : List s.Pos` returns the
  cut positions as byte positions of the input, both ends included.

The reference, the definitions the theorems below are about, is in
`Segmentation/Graphemes.lean`:

- `Segmentation.graphemes : String → List String` splits text into extended
  grapheme clusters.
- `Segmentation.boundaries : String → List Nat` returns the cut positions,
  counted in code points from the start, both ends included.

The two are proved equal by `Segmentation.sliceGraphemes_agree` (see "What is
proved"). Two `@[csimp]` lemmas, `Segmentation.graphemes_eq_graphemesFast` and
`Segmentation.boundaries_eq_boundariesFast`, make compiled calls to
`graphemes` and `boundaries` run the slice scanner, so code that calls the
reference also gets the fast code. The kernel still reduces the reference
definitions themselves.

## What is proved

`Segmentation/Statements.lean` states the claim. It writes the UAX #29 rules
GB1 to GB999 as data (`rules`), in the standard's order, where the first rule
that applies at a position decides it. Each sentence below is one theorem, and
the theorem's type is the committed statement named in brackets.

- Putting the clusters of any text back together gives that text:
  `Segmentation.graphemes_join` (`JoinRestoresInput graphemes`).
- No cluster is the empty string: `Segmentation.graphemes_ne_empty`
  (`ClustersNonEmpty graphemes`).
- In any non-empty text, `graphemes` cuts at a position, the two ends
  included, exactly when the first rule of `rules` that applies there says
  "break", reading the library's own property tables:
  `Segmentation.graphemes_rules` (`CutsMatchRules Tables.props graphemes`).
  The empty text is left out of this statement, because no rule applies to it;
  the two theorems above cover it.
- `boundaries` returns exactly the cut positions of `graphemes`:
  `Segmentation.boundaries_agree` (`BoundariesMatchCuts graphemes boundaries`).

The fast segmenter is proved equal to the reference:

- For any text `s`, the clusters of `sliceGraphemes s.toSlice`, each copied
  into a `String`, are exactly `graphemes s`, and the cuts of
  `sliceBoundaries s.toSlice`, as byte offsets, are `boundaries s` with each
  code-point cut `n` mapped to the UTF-8 size of the first `n` code points:
  `Segmentation.sliceGraphemes_agree`.

The same four statements are proved for the fast scanner's `String` adapters,
`Segmentation.graphemesFast : String → List String` (the clusters of
`sliceGraphemes`, copied into strings) and
`Segmentation.boundariesFast : String → List Nat`:
`Segmentation.graphemesFast_join` (`JoinRestoresInput graphemesFast`),
`Segmentation.graphemesFast_ne_empty` (`ClustersNonEmpty graphemesFast`),
`Segmentation.graphemesFast_rules` (`CutsMatchRules Tables.props graphemesFast`)
and `Segmentation.boundariesFast_agree`
(`BoundariesMatchCuts graphemesFast boundariesFast`).

Each of these nine theorems depends on no axiom beyond `propext`,
`Classical.choice` and `Quot.sound`, the three standard axioms of Lean's logic.
A proof that used `sorry`, `native_decide` or a new `axiom` would depend on an
axiom outside that list.

## Checking the claim yourself

CI runs these checks on every push and pull request. To run them locally, from
the repository root, after `lake test`:

```sh
lake env lean SegmentationDev/Test/HeadlineAxioms.lean
```

This prints the `#print axioms` output for the nine theorems above, and fails
if any of them depends on an axiom outside the three standard ones.
`sh scripts/axiom-gate-self-test.sh` shows that this check can fail: it writes
throwaway files that use `sorry`, `native_decide` and a user `axiom`, and
expects the check to reject each one.

```sh
lake build keyword-scan
git ls-files -z '*.lean' | xargs -0 lake exe keyword-scan
```

This fails if any tracked `.lean` file uses `sorry`, `admit`, `axiom`,
`native_decide`, `implemented_by`, `extern` or `unsafe` as code. The scanner
skips comments, the plain text of string literals and «…» names, because the
test files name these words there as prose, for example in a comment such as
`-- uses no sorry`. The
`{…}` parts of interpolated strings such as `s!"…"` are Lean terms, so it scans
them as code.

```sh
lake build SegmentationDev.Test.GraphemeBreakTestTheorem
```

This proves that `graphemes` matches all 853 test lines of
`GraphemeBreakTest.txt` (see the first item under "What is outside the proof"),
and fails if that proof depends on an axiom outside the three standard ones.
`lake test` does not build it; CI builds it in a step limited to 10 minutes.

`lake test` also pins each theorem's type to its committed statement, so a
theorem renamed, or proved about a weaker statement, fails the tests.

## What is outside the proof

The proofs are about the Lean definitions. These things are not proved, and
you have to trust them, or check them another way:

- **The Unicode data files and the tables generated from them.** The proofs
  read the property tables in `Segmentation/Tables/` as given. These are
  tested, not proved: the data files must match their SHA-256 digests, the
  committed tables must equal what the generator writes from them, `lake test`
  compares the table lookup with the data files for every code point, and
  `graphemes` must agree with all 853 test lines of the Unicode test file
  `GraphemeBreakTest.txt`. That last agreement is also a theorem,
  `SegmentationDev.Test.GraphemeBreakTestTheorem.graphemes_match_graphemeBreakTest`,
  which the kernel checks by `decide +kernel`. It reads the test lines from
  `SegmentationDev/Test/GraphemeBreakTestData.lean`, which `lake exe gen-tables`
  writes from the file; `lake test` and CI fail when that module differs from
  what the file gives. So the theorem is only as good as the file, which is
  trusted like the other data files.
- **The Lean kernel, compiler and runtime.** The kernel checks the proofs. The
  code that runs is compiled from the same definitions by the Lean compiler
  and runs on the Lean runtime, and neither of those is verified.
- **The reading of the rule list against the standard.** `rules` in
  `Segmentation/Statements.lean` is a reading of UAX #29 §3.1.1 into
  data. Nothing proves that this reading is right; you check it by comparing
  the two. The Unicode test file is evidence for it, not a proof.

## How the library was built

An AI system, Descant, built this library. It worked from the issues and
wrote the code, the proofs, the tests and the documentation. It opened a pull
request for each change, and its own reviewer reviewed every pull request. To
read the work, read the repository's merged pull requests and their reviews.

The record of every human touch is this repository's own history on GitHub:
the issues, the pull requests with their reviews and merges, and the commits.
Each commit names its author, so this command lists who wrote each change:

```sh
git log --format='%h %an <%ae> %s'
```

A commit that the pipeline did not author shows a person's name there. A touch
that is not a commit, such as writing an issue or merging a pull request, is
recorded on the issue or pull request itself.

This history was rewritten once, on 2026-11-13, to change the email on the commit that
added the Unicode data files by hand to `tmlayton@users.noreply.github.com`; no file
changed, but every commit after that one has a new ID.

This is the second run of the build. The first run was made in an earlier,
private repository and is not published.

## Prior work

Three Lean projects on Unicode came before this one:

- [UnicodeBasic](https://github.com/fgdorais/lean4-unicode-basic), by
  François G. Dorais, gives Lean the Unicode character properties. It is
  listed on the Lean package index. Its README lists no text segmentation.
- [UnicodeExtra](https://github.com/fgdorais/lean4-unicode-extra), also by
  François G. Dorais, now splits text into grapheme clusters, words and
  sentences. Its CI tests these against the Unicode test files for grapheme,
  word and sentence breaks. Its grapheme code has no correctness proof; this
  library adds one for grapheme clusters.
- [unicode-lean](https://github.com/jpyxal-straylight/unicode-lean) implements
  UAX #29 text segmentation against the Unicode 17.0.0 data. Its theorem that
  grapheme segmentation matches the published Unicode test lines is closed
  with `native_decide`.

This library differs in what this repository shows: it follows UAX #29
revision 49 with the Unicode 18.0.0 data, it proves the theorems under
"What is proved", and none of its proofs uses `native_decide`, which the axiom
check in CI rejects. This section says nothing more about what the other
projects prove than what is written above.

## Using the package

To depend on this package from a project whose Lake configuration is
`lakefile.toml`, add:

```toml
[[require]]
name = "lean-unicode-graphemes"
git = "https://github.com/autnmy/lean-unicode-graphemes"
rev = "main"
```

From a `lakefile.lean`, the package name has to be written in `«»`, because
it contains hyphens:

```lean
require «lean-unicode-graphemes» from git
  "https://github.com/autnmy/lean-unicode-graphemes" @ "main"
```

Then run `lake update`, and write `import Segmentation` in the files that use
the library.

## Building and testing

The toolchain is pinned in `lean-toolchain` (`leanprover/lean4:v4.35.0`).

```sh
lake build   # build the Segmentation library
lake test    # build and run the test suite
```

## Benchmark against UnicodeExtra

The `bench/` directory holds a separate Lake package that times this
library's reference segmenter, `Segmentation.clustersOf` with each cluster
copied into a `String` by `String.ofList`, against UnicodeExtra's
`Unicode.graphemeClusters` on the same inputs. It also times the library's
fast scanner, `Segmentation.sliceGraphemes` on `String.Slice`. Only the
check that compares the clusters copies the fast scanner's slices into
`String`s; the timed calls copy nothing. It is a package of its own so
that the library keeps no dependencies. It depends on this library and on
UnicodeExtra by path, so it builds with no network. Its toolchain, in
`bench/lean-toolchain`, is `leanprover/lean4:v4.35.0`, the library's own.

The benchmark compares against UnicodeExtra. It uses a copy of
UnicodeExtra's source at commit 44228db, with its dependency UnicodeBasic at
7dcace6, kept in bench/vendor/ (both Apache-2.0; each copy carries its
LICENSE). The copies are pinned: they are re-copied by hand to compare
against a newer UnicodeExtra. They build on this library's Lean, 4.35.0,
although upstream targets v4.36.0-rc2. The only changes to the copies are
their lean-toolchain lines and UnicodeExtra finding UnicodeBasic by path;
their Lean code is unchanged. UnicodeBasic uses `extern` and `unsafe` for
its C tables; the copies are third-party code, outside the library and
outside its forbidden-word scan.

**Where it runs.** The workflow `.github/workflows/bench.yml` runs on every
push to `main`, on manual dispatch, and on pull requests that change
`bench/**`, `.github/workflows/bench.yml`, `Segmentation/**`,
`Segmentation.lean`, `lakefile.toml` or `lean-toolchain`, on a GitHub `ubuntu-latest`
runner. The library paths are there because the benchmark builds the library
on its own toolchain, so every library change is also built on
`bench/lean-toolchain`. On a pull request it is an optional check in a
workflow of its own, so a broken benchmark shows up before it lands without
delaying the library's checks. Pull requests that touch none of these paths
do not run it.
The results file records the runner's CPU model, core count and `uname -a`.
In `bench/`, the job runs:

```sh
elan toolchain install "$(cat lean-toolchain)"   # then checks `lean --version` names it
sh build.sh results.md       # build this library, UnicodeExtra, then the benchmark
lake test                    # the input, comparison and report tests
lake exe bench check         # reference, fast and UnicodeExtra clusters must be equal
lake exe bench report results.md
```

`bench report` stops with an error, before timing anything, unless `BENCH_MACHINE`, `BENCH_TOOLCHAIN`,
`BENCH_OURS_COMMIT` and `BENCH_THEIRS_COMMIT` are set, because the results file
records them. The workflow sets all four; to run the report locally, export
them first with the machine, toolchain and commits you are measuring.

Before the plain `check`, the job runs `check --break-ours` and
`check --break-fast`. Each drops the last cluster of one list, and the job
fails unless `check` then exits with status 1 and prints the difference, so
the comparison is shown to catch a difference in either of this library's
segmenters.

If this library, UnicodeExtra, or a module that only imports
both fails to build, `results.md` says which one failed and why, and the job
fails. A failure in the benchmark's own code is reported as a harness
failure, which says nothing about the two libraries.

**Inputs.** Four inputs are generated from a fixed seed: `plain-ascii`;
`mixed-scripts` (Latin with combining marks, CJK, Hangul syllables and jamo,
Indic conjuncts); `emoji` (ZWJ sequences, skin-tone modifiers, flags); and
`large-mixed`, at least 10,000,000 bytes of UTF-8 mixing the other three.
Before anything is timed, `lake exe bench check` compares the clusters of the
reference segmenter, the fast segmenter and UnicodeExtra on every input and
fails with the first difference.

**Timing.** Times are nanoseconds per call, from `IO.monoNanosNow`. Each
small input gets 31 samples of 1000 calls each; `large-mixed` gets 7 samples
of one call each. Each input first gets 2 warm-up samples that are not
counted. The table shows the median and the minimum and maximum. The
reference column ("This library") times `Segmentation.clustersOf` on the
`List Char` of the text, not `graphemes`, because compiled calls to
`graphemes` run the fast scanner. Its time includes copying each cluster into
a new `String`. The fast column times `Segmentation.sliceGraphemes` and
copies nothing; UnicodeExtra's column also counts its slices without copying
them.

**Pass mark.** After the table, the results file lists one line per input
saying whether the fast segmenter's median is at most UnicodeExtra's maximum
sample in the same run, and then both peaks on `large-mixed`. The mark is
reported, not enforced: `bench report` exits 0 either way, so a green run does
not mean the mark was met. Read the lines in `results.md`.

**Memory.** Each input and library runs in a process of its own. The table
shows that process's peak resident memory (`VmHWM` in `/proc/self/status`).
Each peak includes building the input. A baseline process that only builds
the input is shown beside them, and nothing is subtracted.

**What is tested.** The input generator, the comparison, the command-line
parsing, the pass-mark rule and the table's format have tests. The timing and
memory values are measured, not tested.
[`bench/COMPILED-CODE.md`](bench/COMPILED-CODE.md) records a reading of
the C that Lean generates for the timed calls of the reference segmenter and
UnicodeExtra; it predates the fast column, which it does not cover. It quotes
the C that shows both of those segmenting the text on every timed call, and this library
copying each cluster into a new `String` on every call. That reading covers
`leanprover/lean4:v4.35.0` only, the toolchain of the Results table below;
nobody has read the C of the fast column. No check re-reads the C, so a later
source or toolchain change needs a new reading.

**Results.** The table and pass-mark lines below are copied unchanged from
the `bench-results` artifact of
[run 43876245002](https://github.com/autnmy/lean-unicode-graphemes/actions/runs/43876245002)
of `.github/workflows/bench.yml`, a manual dispatch on `main` at commit
`f8c19c2b59845b8c41ffb1dcd1d9b81ebac6c766`, started 2026-11-16T13:29:28Z.
It is the third of three green runs on `main` in a row after the fast column
landed, and the run a maintainer chose for this table; each of the three met
the pass mark on every input. All three segmenters built together on one
toolchain, and the check found the same clusters on every input.

- Machine: AMD EPYC 7763 64-Core Processor, 4 cores, Linux runnervmccnms
  7.0.0-1019-azure #20-Ubuntu SMP PREEMPT Mon Oct 19 22:41:16 UTC 2026
  x86_64 GNU/Linux
- Toolchain: `leanprover/lean4:v4.35.0`
- lean-unicode-graphemes commit: `f8c19c2b59845b8c41ffb1dcd1d9b81ebac6c766`
- UnicodeExtra commit: `44228db53c8104753bf02bff36279a65ea46dce4`

| Input | Samples | Calls per sample | This library median (ns) | This library min-max (ns) | UnicodeExtra median (ns) | UnicodeExtra min-max (ns) | Fast median (ns) | Fast min-max (ns) | Baseline peak (KiB) | This library peak (KiB) | UnicodeExtra peak (KiB) | Fast peak (KiB) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| plain-ascii | 31 | 1000 | 71790 | 71626-72861 | 12521 | 12377-13302 | 8995 | 8963-12977 | 14408 | 14312 | 14408 | 14400 |
| mixed-scripts | 31 | 1000 | 49311 | 49138-49551 | 14010 | 13894-14591 | 7903 | 7875-7987 | 14332 | 14304 | 14324 | 14368 |
| emoji | 31 | 1000 | 24665 | 24626-28273 | 7958 | 7905-8102 | 3961 | 3940-4054 | 14424 | 14400 | 14360 | 14424 |
| large-mixed | 7 | 1 | 2631949456 | 2620302067-2646862048 | 609059851 | 601261525-613354678 | 380170658 | 373978809-391743584 | 43072 | 848628 | 268276 | 389156 |

Pass mark:

- plain-ascii: fast median 8995 ns, UnicodeExtra min-max 12377-13302 ns, fast median at most UnicodeExtra max: yes
- mixed-scripts: fast median 7903 ns, UnicodeExtra min-max 13894-14591 ns, fast median at most UnicodeExtra max: yes
- emoji: fast median 3961 ns, UnicodeExtra min-max 7905-8102 ns, fast median at most UnicodeExtra max: yes
- large-mixed: fast median 380170658 ns, UnicodeExtra min-max 601261525-613354678 ns, fast median at most UnicodeExtra max: yes
- Peak memory on large-mixed: fast 389156 KiB, UnicodeExtra 268276 KiB

## Contributing

Issues and pull requests are welcome. The build pipeline works an issue only
after a maintainer labels it, and automatic pickup is off, so filing an issue
starts nothing by itself.

## Unicode data and generated tables

The Unicode 18.0.0 data files the library reads are committed under
`data/ucd/18.0.0/`, with their SHA-256 digests in `data/ucd/18.0.0/SHA256SUMS`.
`lake test` and CI both check the files against those digests. To check them
by hand, from the repository root:

```sh
(cd data/ucd/18.0.0 && sha256sum --check --strict SHA256SUMS)
```

The property tables in `Segmentation/Tables/GraphemeClusterBreak.lean`,
`Segmentation/Tables/ExtendedPictographic.lean` and
`Segmentation/Tables/IndicConjunctBreak.lean` are generated from those files.
Do not edit them by hand. To regenerate them, from the repository root:

```sh
lake exe gen-tables
```

`lake test` compares the lookup with the data files for every code point, and
fails if the committed tables differ from what the generator writes. CI also
re-runs the generator and fails if any file under `Segmentation/Tables/`
changes.

## Theorem statements

`Segmentation/Statements.lean` states what the library's proofs must show: the
UAX #29 rules written as data, and the partition and boundary theorems. It was
fixed before the segmenter was written, so the statements cannot be bent to fit
the code. CI fails when the file's SHA-256 differs from the line below, so any
change to the statements also has to change this line, in plain view.

```text
40031521b85f84d213492ced77869a86bdd0c6e504959a940dbfa136d43569a6  Segmentation/Statements.lean
```

To check it locally, from the repository root:

```sh
grep -E '^[0-9a-f]{64}  Segmentation/Statements\.lean$' README.md | sha256sum --check --strict
```

## Licence

Apache-2.0; see `LICENSE`. The Unicode Character Database and every table
generated from it are also covered by the Unicode License v3; see `NOTICE`.
