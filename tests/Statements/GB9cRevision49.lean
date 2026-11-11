import Segmentation

open Segmentation in
-- "The GB9c row follows revision 49 verbatim: "GB9c \p{InCB=Linker} \p{InCB=Extend}* × \p{InCB=Consonant}". Revision 47 (Unicode 17) required a consonant before the linker; revision 49 dropped that context."
-- The text before the position is one linker and nothing else. A row that still required
-- a consonant before the linker, as revision 47 did, would make this unprovable.
theorem «GB9c holds after a lone linker with no consonant before it, as revision 49 states» :
    ∃ r, rules[11]? = some r ∧ r.name = "GB9c" ∧
      r.left.Holds [{ gcb := GCB.Extend, extPict := false, incb := InCB.Linker }] ∧
      r.right.Holds [{ gcb := GCB.Other, extPict := false, incb := InCB.Consonant }] := by
  refine ⟨_, rfl, rfl, ?_, ?_⟩
  · exact (⟨[], [{ gcb := GCB.Extend, extPict := false, incb := InCB.Linker }] ++ [], rfl,
      Pat.Matches.seq (Pat.Matches.one rfl) Pat.Matches.starNil⟩ :
      ∃ a b, [({ gcb := GCB.Extend, extPict := false, incb := InCB.Linker } : Props)] = a ++ b ∧
        Pat.Matches (.seq (.one (incbIs .Linker)) (.star (incbIs .Extend))) b)
  · exact (⟨{ gcb := GCB.Other, extPict := false, incb := InCB.Consonant }, [], rfl, rfl⟩ :
      ∃ x rest, [({ gcb := GCB.Other, extPict := false, incb := InCB.Consonant } : Props)] =
        x :: rest ∧ incbIs .Consonant x = true)
