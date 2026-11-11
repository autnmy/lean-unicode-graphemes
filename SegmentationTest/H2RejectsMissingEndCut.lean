import Segmentation

-- "H2, the rules: at every position of a non-empty text, ends included, a cut falls exactly where
-- UAX #29 puts a boundary. The ends make GB1 and GB2 live in the proof."
-- For the text "a", GB2 puts a boundary at position 1 (the end). A segmenter returning no
-- clusters has cut points [0] only, so H2 must not hold for it.
theorem «H2 rejects a segmenter that leaves out the end-of-text cut» :
    ¬ Segmentation.H2 (fun _ => ⟨.Other, false, .None⟩) (fun _ => []) := by
  intro h
  have ht : "a".toList = ['a'] := by first | rfl | decide | simp
  have hb : Segmentation.IsBoundary (fun _ => ⟨.Other, false, .None⟩) ['a'] 1 := by
    refine ⟨1, ⟨"GB2", .ending (.one Segmentation.anyCp), .eot, .brk⟩, rfl, ?_, rfl, ?_⟩
    · simp only [Segmentation.Rule.Applies, Segmentation.Left.Holds, Segmentation.Right.Holds]
      exact ⟨⟨[], _, rfl, .one rfl⟩, rfl⟩
    · intro j r' hj hr' happ
      have hj0 : j = 0 := by omega
      subst hj0
      have hr : r' = ⟨"GB1", .sot Segmentation.nothing, .one Segmentation.anyCp, .brk⟩ := by
        first
          | exact (Option.some.inj hr'.symm)
          | (simp [Segmentation.rules] at hr'; exact hr'.symm)
      subst hr
      simp only [Segmentation.Rule.Applies, Segmentation.Left.Holds, Segmentation.nothing,
        List.take, List.map] at happ
      obtain ⟨hl, _⟩ := happ
      cases hl
      all_goals simp_all
  have hmem := (h "a" 1 (by first | decide | simp) (by first | decide | simp)).mpr (ht ▸ hb)
  first
    | exact absurd hmem (by decide)
    | simp [Segmentation.cutPoints] at hmem
