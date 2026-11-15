import Segmentation
import UnicodeExtra

/-!
# Both libraries in one module

This module holds nothing but the two libraries' imports. CI builds it on its own, after each
library and before any benchmark code. If this library or UnicodeExtra fails to build, or the
two fail when imported together, that failure is a fact about the libraries on the bench
toolchain. A failure in a later step can only be the benchmark's own code.
-/
