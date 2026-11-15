import Bench.Inputs

-- "emoji-heavy text (ZWJ sequences, skin-tone modifiers, flags)"
-- The third input in the issue's order. A flag is two regional indicators in a row.
theorem «inputs emoji text holds ZWJ sequences, skin-tone modifiers and flags» :
    (match (Bench.inputs 42)[2]? with
     | some input =>
       let cs := input.text.toList.map Char.toNat
       let isPictograph := fun c => 0x1F300 ≤ c && c ≤ 0x1FAFF
       let isRegional := fun c => 0x1F1E6 ≤ c && c ≤ 0x1F1FF
       let triples := cs.zip (cs.tail.zip cs.tail.tail)
       triples.any (fun (a, z, b) => isPictograph a && z == 0x200D && isPictograph b) &&
       cs.any (fun c => 0x1F3FB ≤ c && c ≤ 0x1F3FF) &&
       (cs.zip cs.tail).any (fun (a, b) => isRegional a && isRegional b)
     | none => false) = true := by
  decide +kernel
