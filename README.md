# lean-unicode-segmentation
Unicode text segmentation (UAX #29) for Lean 4, with machine-checked proofs

The `Segmentation` library will split text into extended grapheme clusters:
the user-perceived characters that cursor movement, deletion and truncation
should treat as one unit. It follows Unicode 18.0.0 and
[UAX #29 revision 49](https://www.unicode.org/reports/tr29/tr29-49.html), and
uses Lean core only, with no Mathlib, Batteries or other Lake dependencies.

**Status: in progress.** Only the project scaffold exists so far. There is no
segmentation API yet, and nothing in the library is stable.

## Building and testing

The toolchain is pinned in `lean-toolchain` (`leanprover/lean4:v4.35.0`).

```sh
lake build   # build the Segmentation library
lake test    # build and run the test suite
```

## Licence

Apache-2.0; see `LICENSE`. The Unicode Character Database and every table
generated from it are also covered by the Unicode License v3; see `NOTICE`.
