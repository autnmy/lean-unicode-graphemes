# lean-unicode-graphemes
Unicode text segmentation (UAX #29) for Lean 4, with machine-checked proofs

The `Segmentation` library splits text into extended grapheme clusters: the
user-perceived characters that cursor movement, deletion and truncation should
treat as one unit. It follows Unicode 18.0.0 and
[UAX #29 revision 49](https://www.unicode.org/reports/tr29/tr29-49.html)
(`Segmentation/Version.lean` holds both versions), and uses Lean core only,
with no Mathlib, Batteries or other Lake dependencies.

It offers two functions:

- `Segmentation.graphemes : String → List String` splits text into extended
  grapheme clusters.
- `Segmentation.boundaries : String → List Nat` returns the cut positions,
  counted in code points from the start, both ends included.

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

Each of these four theorems depends on no axiom beyond `propext`,
`Classical.choice` and `Quot.sound`, the three standard axioms of Lean's logic.
A proof that used `sorry`, `native_decide` or a new `axiom` would depend on an
axiom outside that list.

## Checking the claim yourself

CI runs these checks on every push and pull request. To run them locally, from
the repository root, after `lake test`:

```sh
lake env lean SegmentationDev/Test/HeadlineAxioms.lean
```

This prints the `#print axioms` output for the four theorems above, and fails
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
revision 49 with the Unicode 18.0.0 data, it proves the four theorems under
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
library's `Segmentation.graphemes` against UnicodeExtra's
`Unicode.graphemeClusters` on the same inputs. It is a package of its own so
that the library keeps no dependencies. It depends on this library by path
and on UnicodeExtra by git at commit `44228db53c81`. It uses its own
toolchain, `leanprover/lean4:v4.36.0-rc2` (in `bench/lean-toolchain`),
because UnicodeExtra at that commit needs it.

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
lake update                  # fetch UnicodeExtra; the log prints the full commit id
sh build.sh results.md       # build this library, UnicodeExtra, then the benchmark
lake test                    # the input, comparison and report tests
lake exe bench check         # both libraries must return the same clusters
lake exe bench report results.md
```

The job fails unless the commit `lake update` resolved starts with
`44228db53c81`. If this library, UnicodeExtra, or a module that only imports
both fails to build, `results.md` says which one failed and why, and the job
fails. A failure in the benchmark's own code is reported as a harness
failure, which says nothing about the two libraries.

**Inputs.** Four inputs are generated from a fixed seed: `plain-ascii`;
`mixed-scripts` (Latin with combining marks, CJK, Hangul syllables and jamo,
Indic conjuncts); `emoji` (ZWJ sequences, skin-tone modifiers, flags); and
`large-mixed`, at least 10,000,000 bytes of UTF-8 mixing the other three.
Before anything is timed, `lake exe bench check` compares the two libraries'
clusters on every input and fails with the first difference.

**Timing.** Times are nanoseconds per call, from `IO.monoNanosNow`. Each
small input gets 31 samples of 1000 calls each; `large-mixed` gets 7 samples
of one call each. Each input first gets 2 warm-up samples that are not
counted. The table shows the median and the minimum and maximum. This
library's time includes copying each cluster into a new `String`;
UnicodeExtra's covers its slices.

**Memory.** Each input and library runs in a process of its own. The table
shows that process's peak resident memory (`VmHWM` in `/proc/self/status`).
Each peak includes building the input. A baseline process that only builds
the input is shown beside them, and nothing is subtracted.

**What is tested.** The input generator, the comparison and the table's
format have tests. The timing and memory values are measured, not tested.

**Results.** The table below is copied unchanged from the `bench-results`
artifact of the first green run of `.github/workflows/bench.yml` on `main`:
[run 43705448890](https://github.com/autnmy/lean-unicode-graphemes/actions/runs/43705448890),
started 2026-11-15T10:43:25Z on a push of commit
`a2d350507c970ca4d346a2e7651380cd428acce4`. Both libraries built together
on one toolchain, and the check found the same clusters on every input.

- Machine: AMD EPYC 7763 64-Core Processor, 4 cores, Linux runnervmccnms
  7.0.0-1019-azure #20-Ubuntu SMP PREEMPT Mon Oct 19 22:41:16 UTC 2026
  x86_64 GNU/Linux
- Toolchain: `leanprover/lean4:v4.36.0-rc2`
- lean-unicode-graphemes commit: `a2d350507c970ca4d346a2e7651380cd428acce4`
- UnicodeExtra commit: `44228db53c8104753bf02bff36279a65ea46dce4`

| Input | Samples | Calls per sample | This library median (ns) | This library min-max (ns) | UnicodeExtra median (ns) | UnicodeExtra min-max (ns) | Baseline peak (KiB) | This library peak (KiB) | UnicodeExtra peak (KiB) |
|---|---|---|---|---|---|---|---|---|---|
| plain-ascii | 31 | 1000 | 65616 | 65440-67950 | 10900 | 10836-11354 | 12140 | 12108 | 12128 |
| mixed-scripts | 31 | 1000 | 45273 | 45173-45554 | 13214 | 13036-13375 | 12348 | 12132 | 12200 |
| emoji | 31 | 1000 | 22085 | 22027-22237 | 6927 | 6874-7037 | 12152 | 12320 | 12372 |
| large-mixed | 7 | 1 | 2369743663 | 2362626317-2380430256 | 511984218 | 506820922-521901586 | 40820 | 781304 | 268128 |

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
