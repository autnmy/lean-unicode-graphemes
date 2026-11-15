import Bench.Inputs

-- The issue lists the inputs in this order: "plain ASCII text; mixed text (Latin with combining
-- marks, CJK, Hangul precomposed and jamo, Indic conjuncts); emoji-heavy text (ZWJ sequences,
-- skin-tone modifiers, flags); and one input of at least 10 MB mixing them". The plan keeps that
-- order, so the ASCII input is the first one.
theorem «inputs puts plain ASCII text first» :
    (match (Bench.inputs 42)[0]? with
     | some input =>
       let cs := input.text.toList.map Char.toNat
       !cs.isEmpty && cs.all (fun c => c < 0x80)
     | none => false) = true := by
  decide +kernel
