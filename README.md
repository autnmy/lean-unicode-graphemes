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
lake env lean SegmentationTest/HeadlineAxioms.lean
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
lake build SegmentationTest.GraphemeBreakTestTheorem
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
  `SegmentationTest.GraphemeBreakTestTheorem.graphemes_match_graphemeBreakTest`,
  which the kernel checks by `decide +kernel`. It reads the test lines from
  `SegmentationTest/GraphemeBreakTestData.lean`, which `lake exe gen-tables`
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

An autonomous coding pipeline built this library. It worked from issues,
wrote the code and the proofs, and opened a pull request for each change.

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
  François G. Dorais, lists "text segmentation into grapheme clusters" in its
  README as a candidate, not as done.
- [unicode-lean](https://github.com/jpyxal-straylight/unicode-lean) implements
  UAX #29 text segmentation against the Unicode 17.0.0 data. Its theorem that
  grapheme segmentation matches the published Unicode test lines is closed
  with `native_decide`.

This library differs in what this repository shows: it follows UAX #29
revision 49 with the Unicode 18.0.0 data, it proves the four theorems under
"What is proved", and none of its proofs uses `native_decide`, which the axiom
check in CI rejects. This section says nothing more about what the other
projects prove than what is written above.

## Building and testing

The toolchain is pinned in `lean-toolchain` (`leanprover/lean4:v4.35.0`).

```sh
lake build   # build the Segmentation library
lake test    # build and run the test suite
```

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
3f96f609b7ee0045ff18e8722cb77a164842981005cde3511b8d54d7c4ee851c  Segmentation/Statements.lean
```

To check it locally, from the repository root:

```sh
grep -E '^[0-9a-f]{64}  Segmentation/Statements\.lean$' README.md | sha256sum --check --strict
```

## Licence

Apache-2.0; see `LICENSE`. The Unicode Character Database and every table
generated from it are also covered by the Unicode License v3; see `NOTICE`.
