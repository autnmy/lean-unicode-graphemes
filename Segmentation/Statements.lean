/-!
# The statements the library proves

The definitions of UAX #29 extended grapheme cluster segmentation that the proofs are checked
against: the code point properties the rules read, the rule table in the standard's order, and
four specification statements about a segmenter `graphemes` and a boundary function `boundaries`.

- `JoinRestoresInput`: the clusters joined back together are the input.
- `ClustersNonEmpty`: no cluster is empty.
- `CutsMatchRules`: on a non-empty text, a cut falls exactly where UAX #29 puts a boundary.
- `BoundariesMatchCuts`: `boundaries` lists the cut points of `graphemes`.

The statements take the property lookup and the segmenter as parameters, so they say nothing
about how either is built. This file imports nothing, and README.md records its SHA-256 digest,
so a change to what the library claims cannot pass unnoticed.
-/

namespace Segmentation

/-- Grapheme_Cluster_Break, UAX #29 Table 2 (Unicode 18.0.0). `Other` is every code point not
listed. -/
inductive GCB where
  | CR | LF | Control | Extend | ZWJ | RI | Prepend | SpacingMark | L | V | T | LV | LVT | Other
  deriving DecidableEq, Repr

/-- Indic_Conjunct_Break, DerivedCoreProperties.txt. -/
inductive InCB where
  | Consonant | Extend | Linker | None
  deriving DecidableEq, Repr

/-- The three properties the rules read, for one code point. -/
structure Props where
  gcb : GCB
  extPict : Bool
  incb : InCB
  deriving DecidableEq, Repr

/-- A class of code points, as a rule names it, e.g. `(Control | CR | LF)`. -/
abbrev Cls := Props → Bool

/-- A pattern over a run of code points, read left to right. -/
inductive Pat where
  | one   (c : Cls)          -- one code point in `c`
  | star  (c : Cls)          -- `c*`
  | pairs (c : Cls)          -- `(c c)*`
  | seq   (p q : Pat)

/-- `Pat.Matches p run` holds when the whole run of code point properties `run` matches the
pattern `p`. -/
inductive Pat.Matches : Pat → List Props → Prop
  | one {c : Cls} {x : Props} : c x = true → Pat.Matches (.one c) [x]
  | starNil {c : Cls} : Pat.Matches (.star c) []
  | starCons {c : Cls} {x : Props} {xs : List Props} :
      c x = true → Pat.Matches (.star c) xs → Pat.Matches (.star c) (x :: xs)
  | pairsNil {c : Cls} : Pat.Matches (.pairs c) []
  | pairsCons {c : Cls} {x y : Props} {xs : List Props} :
      c x = true → c y = true → Pat.Matches (.pairs c) xs →
      Pat.Matches (.pairs c) (x :: y :: xs)
  | seq {p : Pat} {xs : List Props} {q : Pat} {ys : List Props} :
      Pat.Matches p xs → Pat.Matches q ys → Pat.Matches (.seq p q) (xs ++ ys)

/-- The left side of a rule, read against the text before the position. -/
inductive Left where
  | any                          -- nothing written
  | sot     (p : Pat)            -- `sot p`: the whole text before matches `p`
  | ending  (p : Pat)            -- the text before ends with a run matching `p`
  | notThen (c : Cls) (p : Pat)  -- `[^c] p`: that run is preceded by a code point not in `c`

/-- The right side of a rule, read against the text after the position. -/
inductive Right where
  | any | eot | one (c : Cls)

/-- What a rule says about a position: a boundary (÷, `brk`) or no boundary (×, `noBrk`). -/
inductive Verdict where
  | brk | noBrk

/-- One rule of UAX #29: its name in the standard (such as `GB9c`), the text it needs before
and after the position, and its verdict. -/
structure Rule where
  name : String
  left : Left
  right : Right
  verdict : Verdict

/-- A left side holds for `pre`, the properties of the text before the position. -/
def Left.Holds : Left → List Props → Prop
  | .any,         _   => True
  | .sot p,       pre => p.Matches pre
  | .ending p,    pre => ∃ a b, pre = a ++ b ∧ p.Matches b
  | .notThen c p, pre => ∃ a x b, pre = a ++ x :: b ∧ c x = false ∧ p.Matches b

/-- A right side holds for `post`, the properties of the text after the position. -/
def Right.Holds : Right → List Props → Prop
  | .any,   _    => True
  | .eot,   post => post = []
  | .one c, post => ∃ x rest, post = x :: rest ∧ c x = true

/-- The class of every code point, written `Any` in the standard. -/
def anyCp : Cls := fun _ => true
/-- The code points whose Grapheme_Cluster_Break value is one of `gs`. -/
def gcbIn (gs : List GCB) : Cls := fun p => gs.contains p.gcb
/-- The code points with Extended_Pictographic=Yes, written `ExtPict` in the standard. -/
def isExtPict : Cls := fun p => p.extPict
/-- The code points whose Indic_Conjunct_Break value is `v`. -/
def incbIs (v : InCB) : Cls := fun p => p.incb == v
/-- The pattern that matches the empty run only. -/
def nothing : Pat := .star (fun _ => false)

open GCB in
/-- UAX #29 §3.1.1, revision 49, in the standard's order. First match wins. -/
def rules : List Rule := [
  ⟨"GB1",   .sot nothing,                             .one anyCp,                      .brk⟩,
  ⟨"GB2",   .ending (.one anyCp),                     .eot,                            .brk⟩,
  ⟨"GB3",   .ending (.one (gcbIn [CR])),              .one (gcbIn [LF]),               .noBrk⟩,
  ⟨"GB4",   .ending (.one (gcbIn [Control, CR, LF])), .any,                            .brk⟩,
  ⟨"GB5",   .any,                                     .one (gcbIn [Control, CR, LF]),  .brk⟩,
  ⟨"GB6",   .ending (.one (gcbIn [L])),               .one (gcbIn [L, V, LV, LVT]),    .noBrk⟩,
  ⟨"GB7",   .ending (.one (gcbIn [LV, V])),           .one (gcbIn [V, T]),             .noBrk⟩,
  ⟨"GB8",   .ending (.one (gcbIn [LVT, T])),          .one (gcbIn [T]),                .noBrk⟩,
  ⟨"GB9",   .any,                                     .one (gcbIn [Extend, ZWJ]),      .noBrk⟩,
  ⟨"GB9a",  .any,                                     .one (gcbIn [SpacingMark]),      .noBrk⟩,
  ⟨"GB9b",  .ending (.one (gcbIn [Prepend])),         .any,                            .noBrk⟩,
  ⟨"GB9c",  .ending (.seq (.one (incbIs .Linker)) (.star (incbIs .Extend))),
                                                      .one (incbIs .Consonant),        .noBrk⟩,
  ⟨"GB11",  .ending (.seq (.one isExtPict) (.seq (.star (gcbIn [Extend])) (.one (gcbIn [ZWJ])))),
                                                      .one isExtPict,                  .noBrk⟩,
  ⟨"GB12",  .sot (.seq (.pairs (gcbIn [RI])) (.one (gcbIn [RI]))),
                                                      .one (gcbIn [RI]),               .noBrk⟩,
  ⟨"GB13",  .notThen (gcbIn [RI]) (.seq (.pairs (gcbIn [RI])) (.one (gcbIn [RI]))),
                                                      .one (gcbIn [RI]),               .noBrk⟩,
  ⟨"GB999", .ending (.one anyCp),                     .one anyCp,                      .brk⟩ ]

-- The statements take the property lookup and the segmenter as parameters, so this file is
-- committed (L3) before either exists. The final theorems apply them to the library's own
-- `props` (the generated tables), `graphemes` and `boundaries`:
-- `theorem graphemes_join : JoinRestoresInput graphemes := ...`.
variable (props : Char → Props) (graphemes : String → List String)
    (boundaries : String → List Nat)

/-- Rule `r` applies at position `i` (a count of code points) of `cs`. -/
def Rule.Applies (r : Rule) (cs : List Char) (i : Nat) : Prop :=
  r.left.Holds ((cs.take i).map props) ∧ r.right.Holds ((cs.drop i).map props)

/-- UAX #29 puts a boundary at `i` exactly when the first rule that applies there says ÷. -/
def IsBoundary (cs : List Char) (i : Nat) : Prop :=
  ∃ (k : Nat) (r : Rule), rules[k]? = some r ∧ r.Applies props cs i ∧ r.verdict = .brk ∧
    ∀ (j : Nat) (r' : Rule), j < k → rules[j]? = some r' → ¬ r'.Applies props cs i

/-- The positions between the clusters of `gs`, counted in code points from the start. -/
def cutPoints (gs : List String) : List Nat := (gs.map String.length).scanl (· + ·) 0

/-- H1a, partition: the clusters put back together are the input. -/
def JoinRestoresInput : Prop := ∀ s : String, String.join (graphemes s) = s

/-- H1b, partition: none of the clusters is empty. -/
def ClustersNonEmpty : Prop := ∀ s : String, ∀ g ∈ graphemes s, g ≠ ""

/-- H2, the rules: at every position of a non-empty text, ends included, a cut falls exactly
where UAX #29 puts a boundary. The ends make GB1 and GB2 live in the proof. The empty text is
left out because no rule applies to it, while `cutPoints []` is `[0]`; `JoinRestoresInput` and
`ClustersNonEmpty` cover it. -/
def CutsMatchRules : Prop := ∀ (s : String) (i : Nat), s ≠ "" → i ≤ s.length →
  (i ∈ cutPoints (graphemes s) ↔ IsBoundary props s.toList i)

/-- H2', the two functions agree: `boundaries` lists the cut points of `graphemes`. -/
def BoundariesMatchCuts : Prop := ∀ s : String, boundaries s = cutPoints (graphemes s)

end Segmentation
