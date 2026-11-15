import Bench.Inputs

-- "mixed text (Latin with combining marks, CJK, Hangul precomposed and jamo, Indic conjuncts)"
-- The second input in the issue's order. A conjunct is a consonant, a virama, then a consonant;
-- the viramas listed are those of the main Indic scripts, so any of them counts.
theorem «inputs mixed text holds combining marks, CJK, Hangul syllables and jamo, and Indic conjuncts» :
    (match (Bench.inputs 42)[1]? with
     | some input =>
       let cs := input.text.toList.map Char.toNat
       let viramas := [0x094D, 0x09CD, 0x0A4D, 0x0ACD, 0x0B4D, 0x0BCD, 0x0C4D, 0x0CCD, 0x0D4D]
       let isLetter := fun c => (0x0900 ≤ c && c ≤ 0x0D7F) && !viramas.contains c
       let pairs := cs.zip cs.tail
       let triples := cs.zip (cs.tail.zip cs.tail.tail)
       cs.any (fun c => 0x0041 ≤ c && c ≤ 0x007A) &&
       cs.any (fun c => 0x0300 ≤ c && c ≤ 0x036F) &&
       cs.any (fun c => 0x4E00 ≤ c && c ≤ 0x9FFF) &&
       cs.any (fun c => 0xAC00 ≤ c && c ≤ 0xD7A3) &&
       pairs.any (fun (l, v) => 0x1100 ≤ l && l ≤ 0x115F && 0x1160 ≤ v && v ≤ 0x11A7) &&
       triples.any (fun (a, b, c) => isLetter a && viramas.contains b && isLetter c)
     | none => false) = true := by
  decide +kernel
