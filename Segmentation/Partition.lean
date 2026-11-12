import Segmentation.Statements
import Segmentation.Graphemes

/-!
# The clusters partition the text

Proofs of `H1a` and `H1b` from `Segmentation.Statements` for `graphemes`: the clusters joined
back together are the input, and no cluster is empty.

Neither fact depends on where the rules put the breaks, so both are proved first for the
`List Char` core `clustersOf` with any property lookup, then carried to `String` through
core's `String.toList` lemmas. The `clustersOf` lemmas are public so other proofs about the
same core can use them.
-/

namespace Segmentation

/-- The clusters `clustersOf.go` returns, flattened, are the open cluster (stored newest code
point first) followed by the rest of the input. -/
theorem clustersOf_go_flatten (props : Char → Props) :
    ∀ (rest : List Char) (s : ScanState) (cluster : List Char),
      (clustersOf.go props s cluster rest).flatten = cluster.reverse ++ rest
  | [], _, _ => by simp [clustersOf.go]
  | c :: rest, s, cluster => by
    unfold clustersOf.go
    dsimp only
    split
    · simp [clustersOf_go_flatten props rest]
    · simp [clustersOf_go_flatten props rest]

/-- The clusters of `cs`, flattened, are `cs`. -/
theorem clustersOf_flatten (props : Char → Props) (cs : List Char) :
    (clustersOf props cs).flatten = cs := by
  cases cs with
  | nil => simp [clustersOf]
  | cons c rest => simp [clustersOf, clustersOf_go_flatten]

/-- When the open cluster is not empty, no cluster `clustersOf.go` returns is empty: it only
ever opens a new cluster with the code point that starts it. -/
theorem clustersOf_go_ne_nil (props : Char → Props) :
    ∀ (rest : List Char) (s : ScanState) (cluster : List Char), cluster ≠ [] →
      ∀ g ∈ clustersOf.go props s cluster rest, g ≠ []
  | [], _, _, h => by simpa [clustersOf.go] using h
  | c :: rest, s, cluster, h => by
    unfold clustersOf.go
    dsimp only
    split
    · intro g hg
      simp only [List.mem_cons] at hg
      rcases hg with rfl | hg
      · simpa using h
      · exact clustersOf_go_ne_nil props rest _ [c] (by simp) g hg
    · exact clustersOf_go_ne_nil props rest _ (c :: cluster) (by simp)

/-- No cluster of `cs` is empty. -/
theorem clustersOf_ne_nil (props : Char → Props) (cs : List Char) :
    ∀ g ∈ clustersOf props cs, g ≠ [] := by
  cases cs with
  | nil => simp [clustersOf]
  | cons c rest => exact clustersOf_go_ne_nil props rest _ [c] (by simp)

/-- `H1a` for `graphemes`: the clusters joined back together are the input. -/
theorem graphemes_join : H1a graphemes := by
  intro s
  apply String.ext
  simp [graphemes, String.toList_join, List.flatMap, Function.comp_def, String.toList_ofList,
    clustersOf_flatten]

/-- `H1b` for `graphemes`: no cluster is the empty string. -/
theorem graphemes_ne_empty : H1b graphemes := by
  intro s g hg
  simp only [graphemes, List.mem_map] at hg
  obtain ⟨l, hl, rfl⟩ := hg
  rw [Ne, String.ofList_eq_empty_iff]
  exact clustersOf_ne_nil Tables.props s.toList l hl

end Segmentation
