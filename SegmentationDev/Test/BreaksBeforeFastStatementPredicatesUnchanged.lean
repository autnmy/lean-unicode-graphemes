import Segmentation

-- "`Segmentation/Statements.lean` stays byte-for-byte unchanged, because its SHA-256 is pinned in
-- the README and checked by the first step of `.github/workflows/ci.yml`."
-- The SHA-256 check in CI covers the bytes. This test covers one way a proof could be made to go
-- through: editing the predicates the equality depends on. It pins `gcbIn`, `incbIs` and
-- `isExtPict` to their definitions, and uses the equality on a GB11 case, where all three apply.
/-- The equality holds while `gcbIn`, `incbIs` and `isExtPict` keep their definitions from `Statements.lean`. -/
theorem breaksBeforeFast_eq_uses_unchanged_statement_predicates :
    (∀ (gs : List Segmentation.GCB) (p : Segmentation.Props),
        Segmentation.gcbIn gs p = gs.contains p.gcb) ∧
    (∀ (v : Segmentation.InCB) (p : Segmentation.Props),
        Segmentation.incbIs v p = (p.incb == v)) ∧
    (∀ p : Segmentation.Props, Segmentation.isExtPict p = p.extPict) ∧
    Segmentation.breaksBeforeFast
        ⟨⟨.zwj, false, .none⟩, false, false, true, false⟩ ⟨.other, true, .none⟩ =
      Segmentation.breaksBefore
        ⟨⟨.zwj, false, .none⟩, false, false, true, false⟩ ⟨.other, true, .none⟩ :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl,
    Segmentation.breaksBeforeFast_eq_breaksBefore _ _⟩
