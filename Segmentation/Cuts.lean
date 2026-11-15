import Segmentation.Statements
import Segmentation.Graphemes
import Segmentation.ScanInvariants

/-!
# Where the clusters cut the text

`mem_cutsOf` says which positions `cutsOf` lists: both ends of the text, and each position inside
it where `breaksBefore` says ÷ for the scan state that has read every code point before it. It
holds for any property lookup. `boundaries_agree` proves `BoundariesMatchCuts`: `boundaries`
lists the cut points of `graphemes`.

`clustersOf.go` reads the text one code point at a time, so `mem_cutsOf` is proved through a
lemma about `go` part way through the text. That lemma names the scan state by the properties
already read, and the start of the open cluster by the running total `scanl` has reached, so the
same statement holds again after `go` reads the next code point.
-/

namespace Segmentation

/-- Reading one more code point pushes its properties onto the scan state. -/
private theorem scanStateOf_append_singleton (p q : Props) (ps : List Props) :
    scanStateOf p (ps ++ [q]) = (scanStateOf p ps).push q := by
  simp [scanStateOf, List.foldl_append]

/-- The positions inside `rest` where the scan says ÷, after it has read `p :: ps` and then the
part of `rest` before the position. Positions count from the start of `p :: ps`. -/
private def CutInside (props : Char → Props) (p : Props) (ps : List Props) (rest : List Char)
    (i : Nat) : Prop :=
  ∃ (j : Nat) (h : j < rest.length), i = ps.length + 1 + j ∧
    breaksBefore (scanStateOf p (ps ++ (rest.take j).map props)) (props rest[j]) = true

/-- A cut inside `d :: rest` is either just before `d`, or a cut inside `rest` once `d` is read. -/
private theorem cutInside_cons (props : Char → Props) (p : Props) (ps : List Props) (d : Char)
    (rest : List Char) (i : Nat) :
    CutInside props p ps (d :: rest) i ↔
      (i = ps.length + 1 ∧ breaksBefore (scanStateOf p ps) (props d) = true) ∨
        CutInside props p (ps ++ [props d]) rest i := by
  constructor
  · rintro ⟨j, hj, rfl, hb⟩
    cases j with
    | zero => exact Or.inl ⟨rfl, by simpa using hb⟩
    | succ j =>
      refine Or.inr ⟨j, by simpa using hj, by simp; omega, ?_⟩
      simpa [List.take_succ_cons, List.append_assoc] using hb
  · rintro (⟨rfl, hb⟩ | ⟨j, hj, rfl, hb⟩)
    · exact ⟨0, by simp, by simp, by simpa using hb⟩
    · refine ⟨j + 1, by simpa using hj, by simp; omega, ?_⟩
      simpa [List.take_succ_cons, List.append_assoc] using hb

/-- The cut points of what `clustersOf.go` returns, started from `a`. The scan has read `p :: ps`,
and the open cluster holds the last `cluster.length` of those code points, so it starts at `a`. -/
private theorem mem_scanl_go (props : Char → Props) (p : Props) (i : Nat) :
    ∀ (rest : List Char) (ps : List Props) (cluster : List Char) (a : Nat),
      ps.length + 1 = a + cluster.length →
      (i ∈ ((clustersOf.go props (scanStateOf p ps) cluster rest).map List.length).scanl
          (· + ·) a ↔
        i = a ∨ i = ps.length + 1 + rest.length ∨ CutInside props p ps rest i)
  | [], ps, cluster, a, h => by
    simp only [clustersOf.go, List.map_cons, List.map_nil, List.scanl_cons, List.scanl_nil,
      List.mem_cons, List.length_reverse, List.not_mem_nil, List.length_nil]
    have : ¬ CutInside props p ps [] i := fun ⟨_, hj, _⟩ => absurd hj (by simp)
    constructor
    · rintro (h1 | h1 | h1)
      · exact Or.inl h1
      · exact Or.inr (Or.inl (by omega))
      · exact h1.elim
    · rintro (h1 | h1 | h1)
      · exact Or.inl h1
      · exact Or.inr (Or.inl (by omega))
      · exact (this h1).elim
  | d :: rest, ps, cluster, a, h => by
    rw [cutInside_cons]
    unfold clustersOf.go
    dsimp only
    rw [← scanStateOf_append_singleton]
    split
    · rename_i hb
      simp only [List.map_cons, List.scanl_cons, List.mem_cons, List.length_reverse]
      rw [mem_scanl_go props p i rest (ps ++ [props d]) [d] (a + cluster.length)
        (by simp; omega)]
      simp only [List.length_append, List.length_cons, List.length_nil]
      constructor
      · rintro (h1 | h1 | h1 | h1)
        · exact Or.inl h1
        · exact Or.inr (Or.inr (Or.inl ⟨by omega, hb⟩))
        · exact Or.inr (Or.inl (by omega))
        · exact Or.inr (Or.inr (Or.inr h1))
      · rintro (h1 | h1 | ⟨h1, _⟩ | h1)
        · exact Or.inl h1
        · exact Or.inr (Or.inr (Or.inl (by omega)))
        · exact Or.inr (Or.inl (by omega))
        · exact Or.inr (Or.inr (Or.inr h1))
    · rename_i hb
      rw [mem_scanl_go props p i rest (ps ++ [props d]) (d :: cluster) a (by simp; omega)]
      simp only [List.length_append, List.length_cons, List.length_nil]
      constructor
      · rintro (h1 | h1 | h1)
        · exact Or.inl h1
        · exact Or.inr (Or.inl (by omega))
        · exact Or.inr (Or.inr (Or.inr h1))
      · rintro (h1 | h1 | ⟨_, h1⟩ | h1)
        · exact Or.inl h1
        · exact Or.inr (Or.inl (by omega))
        · exact absurd h1 hb
        · exact Or.inr (Or.inr h1)

/-- The cut points of a non-empty text are its two ends and each position inside it where the
scan, having read every code point before the position, says ÷ before the next one. -/
theorem mem_cutsOf (props : Char → Props) (c : Char) (cs : List Char) (i : Nat) :
    i ∈ cutsOf props (c :: cs) ↔ i = 0 ∨ i = cs.length + 1 ∨
      ∃ (j : Nat) (h : j < cs.length), i = j + 1 ∧
        breaksBefore (scanStateOf (props c) ((cs.take j).map props)) (props cs[j]) = true := by
  have hgo := mem_scanl_go props (props c) i cs [] [c] 0 (by simp)
  have hstart : scanStateOf (props c) [] = ScanState.start (props c) := rfl
  rw [hstart] at hgo
  simp only [cutsOf, clustersOf]
  rw [hgo]
  simp only [CutInside, List.length_nil, List.nil_append]
  constructor
  · rintro (h1 | h1 | ⟨j, hj, h1, hb⟩)
    · exact Or.inl h1
    · exact Or.inr (Or.inl (by omega))
    · exact Or.inr (Or.inr ⟨j, hj, by omega, hb⟩)
  · rintro (h1 | h1 | ⟨j, hj, h1, hb⟩)
    · exact Or.inl h1
    · exact Or.inr (Or.inl (by omega))
    · exact Or.inr (Or.inr ⟨j, hj, by omega, hb⟩)

/-- `BoundariesMatchCuts` for `graphemes` and `boundaries`: `boundaries` lists the cut points of
`graphemes`. A cluster turned into a string keeps its length in code points, so both sides add
up the same lengths. -/
theorem boundaries_agree : BoundariesMatchCuts graphemes boundaries := by
  intro s
  simp [boundaries, cutsOf, cutPoints, graphemes, List.map_map, Function.comp_def,
    String.length_ofList]

end Segmentation
