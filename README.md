# lean-unicode-segmentation
Unicode text segmentation (UAX #29) for Lean 4, with machine-checked proofs

The `Segmentation` library will split text into extended grapheme clusters:
the user-perceived characters that cursor movement, deletion and truncation
should treat as one unit. It follows Unicode 18.0.0 and
[UAX #29 revision 49](https://www.unicode.org/reports/tr29/tr29-49.html), and
uses Lean core only, with no Mathlib, Batteries or other Lake dependencies.

**Status: in progress.** The project scaffold and the theorem statements exist
so far. There is no segmentation API yet, and nothing in the library is stable.

## Building and testing

The toolchain is pinned in `lean-toolchain` (`leanprover/lean4:v4.35.0`).

```sh
lake build   # build the Segmentation library
lake test    # build and run the test suite
```

## Theorem statements

`Segmentation/Statements.lean` states what the library's proofs must show: the
UAX #29 rules written as data, and the partition and boundary theorems. It was
fixed before the segmenter was written, so the statements cannot be bent to fit
the code. CI fails when the file's SHA-256 differs from the line below, so any
change to the statements also has to change this line, in plain view.

```text
5e784ba330c7a11857b00674311904ffb7c22334e7ed895055b558a1218708bf  Segmentation/Statements.lean
```

To check it locally, from the repository root:

```sh
grep -E '^[0-9a-f]{64}  Segmentation/Statements\.lean$' README.md | sha256sum --check --strict
```

## Licence

Apache-2.0; see `LICENSE`. The Unicode Character Database and every table
generated from it are also covered by the Unicode License v3; see `NOTICE`.
