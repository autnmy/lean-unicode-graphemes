/-!
# Benchmark inputs

The four texts both libraries segment, built from a fixed seed so every run measures the same
bytes. Each text is a run of pieces: short code point sequences that each show one feature the
benchmark must cover (a combining mark, a jamo run, a ZWJ sequence, a flag). Every piece is
written as code point numbers, because Lean's `\u` string escape takes exactly four hex digits
and cannot spell code points above U+FFFF. The numbers are fixed valid scalar values, never
drawn at random, so `Char.ofNat` never meets a surrogate or an out-of-range value and turns it
into U+0000.

Each small input starts with every one of its pieces once, so each feature is present whatever
the random draw gives, and then continues with pieces picked at random.
-/

namespace Bench

/-- One benchmark input and the name the results show for it. -/
structure NamedInput where
  name : String
  text : String

/-- The seed every benchmark run uses. -/
def fixedSeed : UInt64 := 42

/-- The four kinds of input, in the order the issue lists them and the results show them. -/
inductive InputKind where
  | plainAscii
  | mixedScripts
  | emoji
  | largeMixed
  deriving DecidableEq, Repr

namespace InputKind

def all : List InputKind := [.plainAscii, .mixedScripts, .emoji, .largeMixed]

def name : InputKind → String
  | .plainAscii => "plain-ascii"
  | .mixedScripts => "mixed-scripts"
  | .emoji => "emoji"
  | .largeMixed => "large-mixed"

/-- Mixed into the seed so each kind draws its own random sequence. -/
def stream : InputKind → UInt64
  | .plainAscii => 1
  | .mixedScripts => 2
  | .emoji => 3
  | .largeMixed => 4

end InputKind

/-- The state of a SplitMix64 generator: small, fast, and fully determined by its seed. -/
structure Rng where
  state : UInt64

/-- The next 64-bit value of SplitMix64 and the advanced state. -/
def Rng.next (g : Rng) : UInt64 × Rng :=
  let s := g.state + 0x9E3779B97F4A7C15
  let z := (s ^^^ (s >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (z ^^^ (z >>> 31), ⟨s⟩)

/-- A short code point sequence that shows one feature of the text. -/
abbrev Piece := List Nat

/-- English words, each followed by a space or punctuation. -/
def asciiPieces : List Piece :=
  ["the ", "quick ", "brown ", "fox ", "jumps ", "over ", "lazy ", "dog ", "and ", "runs ",
    "Lean ", "proves ", "it. ", "Then, ", "42 ", "times!\n"].map fun w => w.toList.map Char.toNat

/-- Latin with combining marks, CJK, Hangul syllables and jamo, and Indic conjuncts. -/
def mixedPieces : List Piece :=
  [ [0x63, 0x61, 0x66, 0x65, 0x0301, 0x20],          -- "cafe" with a combining acute accent
    [0x6E, 0x0303, 0x61, 0x0308, 0x20],              -- n with tilde, a with diaeresis
    [0x4E2D, 0x6587],                                -- CJK ideographs
    [0x65E5, 0x672C, 0x8A9E, 0x20],                  -- CJK ideographs
    [0xD55C, 0xAE00, 0x20],                          -- precomposed Hangul syllables
    [0x1112, 0x1161, 0x11AB],                        -- Hangul jamo L V T
    [0x1100, 0x1161],                                -- Hangul jamo L V
    [0x0915, 0x094D, 0x0937, 0x20],                  -- Devanagari conjunct (ka, virama, ssa)
    [0x0995, 0x09CD, 0x09B7, 0x20],                  -- Bengali conjunct (ka, virama, ssa)
    [0x0928, 0x092E, 0x0938, 0x094D, 0x0924, 0x0947, 0x20] ]  -- Devanagari word with a conjunct

/-- ZWJ sequences, skin-tone modifiers and flags. -/
def emojiPieces : List Piece :=
  [ [0x1F468, 0x200D, 0x1F469, 0x200D, 0x1F467],     -- family, joined by ZWJ
    [0x1F469, 0x1F3FE, 0x200D, 0x1F4BB],             -- technologist with a skin tone, ZWJ
    [0x1F44D, 0x1F3FD],                              -- thumbs up with a skin tone
    [0x1F1EB, 0x1F1F7],                              -- flag: two regional indicators
    [0x1F1EF, 0x1F1F5],                              -- flag: two regional indicators
    [0x1F600],                                       -- single emoji
    [0x20] ]

/-- How many random pieces follow the fixed opening of a small input. The bench tests decode the
small inputs in the kernel (`decide +kernel`), whose cost grows faster than the text's length, so
the small inputs stay short; the large input is where the volume is. -/
def smallPieceCount : Nat := 20

/-- The large input reaches at least 10 MiB, which is also at least 10,000,000 bytes. -/
def largeByteTarget : Nat := 10 * 1024 * 1024

/-- A piece picked at random from a non-empty list. -/
def pick (pieces : List Piece) (g : Rng) : Piece × Rng :=
  let (r, g') := g.next
  (pieces.getD (r.toNat % pieces.length) [], g')

/-- The code points of `count` pieces picked at random. -/
def randomPieces (pieces : List Piece) : (count : Nat) → Rng → List Nat
  | 0, _ => []
  | count + 1, g =>
    let (p, g') := pick pieces g
    p ++ randomPieces pieces count g'

def pushCodePoints (acc : String) (cps : List Nat) : String :=
  cps.foldl (fun s c => s.push (Char.ofNat c)) acc

/-- Appends random pieces to `acc` until it holds at least `target` bytes. Every piece adds at
least one byte, so `target` steps of fuel always suffice. -/
def fillTo (pieces : List Piece) (target : Nat) : (fuel : Nat) → Rng → String → String
  | 0, _, acc => acc
  | fuel + 1, g, acc =>
    if acc.utf8ByteSize ≥ target then acc
    else
      let (p, g') := pick pieces g
      fillTo pieces target fuel g' (pushCodePoints acc p)

/-- The text of a small input: every piece once, then random pieces. -/
def smallText (pieces : List Piece) (g : Rng) : String :=
  String.ofList ((pieces.flatten ++ randomPieces pieces smallPieceCount g).map Char.ofNat)

/-- The input of one kind, built from `seed`. -/
def input (seed : UInt64) (kind : InputKind) : NamedInput :=
  let g : Rng := ⟨seed ^^^ kind.stream⟩
  let text := match kind with
    | .plainAscii => smallText asciiPieces g
    | .mixedScripts => smallText mixedPieces g
    | .emoji => smallText emojiPieces g
    | .largeMixed =>
      let pieces := asciiPieces ++ mixedPieces ++ emojiPieces
      fillTo pieces largeByteTarget largeByteTarget g (pushCodePoints "" pieces.flatten)
  { name := kind.name, text }

/-- All four inputs, in the order of `InputKind.all`. -/
def inputs (seed : UInt64) : List NamedInput :=
  InputKind.all.map (input seed)

end Bench
