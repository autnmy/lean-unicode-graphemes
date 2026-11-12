/-!
# The forbidden-word rule

Project code may not use `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `extern` or
`unsafe`: each one either leaves a proof unfinished or lets code run that the kernel never checks.
A plain text search cannot enforce this, because the test files name these words in comments,
in strings and in «…» theorem names. `findForbidden` first blanks out that prose, then reports
each identifier part that equals a forbidden word.

What counts as prose: `--` comments, `/- … -/` comments (they nest, and doc comments are
included), character literals, the text of string literals (raw ones such as `r#"…"#` too), and
«…» names. The `{…}` parts of an interpolated string, such as `s!"…"`, `m!"…"` or the string
after `throwError` or `dbg_trace`, hold Lean terms, so they are scanned as code.
-/

namespace Gate

/-- The words project code may not use, in the order the rule lists them. -/
def forbiddenWords : List String :=
  ["sorry", "admit", "axiom", "native_decide", "implemented_by", "extern", "unsafe"]

/-- The kind of text the scanner is inside. -/
private inductive Region where
  | code
  | lineComment
  /-- Inside `depth` nested block comments. -/
  | blockComment (depth : Nat)
  /-- Inside a string literal; an interpolated one opens code at each `{`. -/
  | string (interpolated : Bool)
  /-- Inside a raw string literal such as `r"…"` or `r#"…"#`, opened with `hashes` `#` signs.
  A raw string has no escapes, so a backslash in it is plain text. -/
  | rawString (hashes : Nat)
  /-- After a `"` inside a raw string, waiting for `remaining` more of its closing `#` signs. -/
  | rawStringEnd (hashes remaining : Nat)
  /-- Inside a character literal that starts with an escape, such as `'\n'`, after the escaped
  character. -/
  | charLiteral
  | quotedName

/-- Characters that can continue an identifier part. Anything else, `.` included, ends one, so
`Lean.sorry` and `foo.unsafe` are still caught while `sorryAx` and `axioms` are other words.
Non-ASCII characters end a part too: that can only report more, never hide a word. -/
private def isWordChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '\''

/-- Prose keeps its line breaks so the line numbers of the code stay right. -/
private def blank (c : Char) : Char :=
  if c == '\n' then '\n' else ' '

/-- `before` with its last `(…)` group removed; `depth` counts the `)` still to be matched. -/
private def dropParenGroup : List Char → Nat → List Char
  | [], _ => []
  | ')' :: rest, depth => dropParenGroup rest (depth + 1)
  | '(' :: rest, depth => if depth ≤ 1 then rest else dropParenGroup rest (depth - 1)
  | _ :: rest, depth => dropParenGroup rest depth

/-- `before` without its last term, when that term is a name or a `(…)` group, and without the
whitespace in front of that term. -/
private def dropTerm (before : List Char) : List Char :=
  let rest := match before with
    | ')' :: _ => dropParenGroup before 0
    | _ => before.dropWhile fun c => isWordChar c || c == '.'
  rest.dropWhile Char.isWhitespace

/-- Whether `before` ends with the keyword `word`, not with a longer name that contains it. -/
private def endsWithKeyword (before : List Char) (word : String) : Bool :=
  let reversed := word.toList.reverse
  before.take reversed.length == reversed &&
    match before.drop reversed.length with
    | c :: _ => !isWordChar c && c != '.'
    | [] => true

/-- Whether a `"` that follows `before` opens a string whose `{…}` parts are Lean terms. That
holds after a `!` macro such as `s!` or `m!`, after `]` as in `trace[cls] "…"`, and after
`throwError`, `dbg_trace` or `throwErrorAt ref`, which take such a string without a `!`. Taking
`]` too can only scan more text as code, so it can only report more. -/
private def opensInterpolatedString (before : List Char) : Bool :=
  let before := before.dropWhile Char.isWhitespace
  match before with
  | '!' :: _ | ']' :: _ => true
  | _ =>
    endsWithKeyword before "throwError" || endsWithKeyword before "dbg_trace" ||
      endsWithKeyword (dropTerm before) "throwErrorAt"

/-- The number of `#` signs when a `"` that follows `before` opens a raw string (`r"`, `r#"`,
…), or `none` when it opens an ordinary string. -/
private def rawStringHashes (before : List Char) : Option Nat :=
  let hashes := (before.takeWhile (· == '#')).length
  match before.drop hashes with
  | 'r' :: c :: _ => if isWordChar c || c == '.' then none else some hashes
  | ['r'] => some hashes
  | _ => none

/-- The region a `"` in code opens. `before` is the code so far, last character first. -/
private def stringRegion (before : List Char) : Region :=
  match rawStringHashes before with
  | some hashes => .rawString hashes
  | none => .string (opensInterpolatedString before)

/-- `cs` with every prose character replaced by a space, built in reverse onto `out`.
`braces` has one entry for each open `{…}` part of an interpolated string: the number of `{`
opened inside that part that are still unclosed. `prev` is the last code character, used to tell
a character literal from the prime in a name like `h'`. The kind of string a `"` opens is read
from the code already in `out`. -/
private def blankProse : List Char → Region → List Nat → Char → List Char → List Char
  | [], _, _, _, out => out.reverse
  | '-' :: '-' :: rest, .code, braces, _, out =>
    blankProse rest .lineComment braces ' ' (' ' :: ' ' :: out)
  | '/' :: '-' :: rest, .code, braces, _, out =>
    blankProse rest (.blockComment 1) braces ' ' (' ' :: ' ' :: out)
  | '"' :: rest, .code, braces, _, out =>
    blankProse rest (stringRegion out) braces ' ' (' ' :: out)
  | '«' :: rest, .code, braces, _, out =>
    blankProse rest .quotedName braces ' ' (' ' :: out)
  | '\'' :: rest, .code, braces, prev, out =>
    if isWordChar prev then
      blankProse rest .code braces '\'' ('\'' :: out)
    else
      -- The equation lets the termination proof see that `rest` is shorter in the last branch.
      match _h : rest with
      -- The escaped character is taken with the backslash, so `'\\'` and `'\''` close on
      -- their last quote.
      | '\\' :: c :: afterEscape =>
        blankProse afterEscape .charLiteral braces ' ' (blank c :: ' ' :: ' ' :: out)
      | c :: '\'' :: afterLiteral =>
        blankProse afterLiteral .code braces ' ' (' ' :: blank c :: ' ' :: out)
      | _ => blankProse rest .code braces '\'' ('\'' :: out)
  | '{' :: rest, .code, braces, _, out =>
    let braces := match braces with
      | open_ :: outer => (open_ + 1) :: outer
      | [] => []
    blankProse rest .code braces '{' ('{' :: out)
  | '}' :: rest, .code, braces, _, out =>
    match braces with
    | 0 :: outer => blankProse rest (.string true) outer ' ' (' ' :: out)
    | (open_ + 1) :: outer => blankProse rest .code (open_ :: outer) '}' ('}' :: out)
    | [] => blankProse rest .code [] '}' ('}' :: out)
  | c :: rest, .code, braces, _, out =>
    blankProse rest .code braces c (c :: out)
  | '\n' :: rest, .lineComment, braces, _, out =>
    blankProse rest .code braces '\n' ('\n' :: out)
  | c :: rest, .lineComment, braces, prev, out =>
    blankProse rest .lineComment braces prev (blank c :: out)
  | '/' :: '-' :: rest, .blockComment depth, braces, prev, out =>
    blankProse rest (.blockComment (depth + 1)) braces prev (' ' :: ' ' :: out)
  | '-' :: '/' :: rest, .blockComment depth, braces, prev, out =>
    let region := if depth ≤ 1 then .code else .blockComment (depth - 1)
    blankProse rest region braces prev (' ' :: ' ' :: out)
  | c :: rest, .blockComment depth, braces, prev, out =>
    blankProse rest (.blockComment depth) braces prev (blank c :: out)
  | '\\' :: c :: rest, .string interpolated, braces, prev, out =>
    blankProse rest (.string interpolated) braces prev (blank c :: ' ' :: out)
  | '"' :: rest, .string _, braces, _, out =>
    blankProse rest .code braces ' ' (' ' :: out)
  | '{' :: rest, .string true, braces, _, out =>
    blankProse rest .code (0 :: braces) ' ' (' ' :: out)
  | c :: rest, .string interpolated, braces, prev, out =>
    blankProse rest (.string interpolated) braces prev (blank c :: out)
  | '"' :: rest, .rawString 0, braces, _, out =>
    blankProse rest .code braces ' ' (' ' :: out)
  | '"' :: rest, .rawString hashes, braces, prev, out =>
    blankProse rest (.rawStringEnd hashes hashes) braces prev (' ' :: out)
  | c :: rest, .rawString hashes, braces, prev, out =>
    blankProse rest (.rawString hashes) braces prev (blank c :: out)
  | '#' :: rest, .rawStringEnd hashes remaining, braces, prev, out =>
    if remaining ≤ 1 then
      blankProse rest .code braces ' ' (' ' :: out)
    else
      blankProse rest (.rawStringEnd hashes (remaining - 1)) braces prev (' ' :: out)
  | '"' :: rest, .rawStringEnd hashes _, braces, prev, out =>
    blankProse rest (.rawStringEnd hashes hashes) braces prev (' ' :: out)
  | c :: rest, .rawStringEnd hashes _, braces, prev, out =>
    blankProse rest (.rawString hashes) braces prev (blank c :: out)
  | '\\' :: c :: rest, .charLiteral, braces, prev, out =>
    blankProse rest .charLiteral braces prev (blank c :: ' ' :: out)
  | '\'' :: rest, .charLiteral, braces, _, out =>
    blankProse rest .code braces ' ' (' ' :: out)
  | c :: rest, .charLiteral, braces, prev, out =>
    blankProse rest .charLiteral braces prev (blank c :: out)
  | '»' :: rest, .quotedName, braces, _, out =>
    blankProse rest .code braces ' ' (' ' :: out)
  | c :: rest, .quotedName, braces, prev, out =>
    blankProse rest .quotedName braces prev (blank c :: out)
termination_by cs => cs.length

/-- The forbidden words among the identifier parts of `code`, each with its 1-based line. -/
private def forbiddenParts (code : List Char) : List (Nat × String) :=
  let flush (line : Nat) (part : String) (found : List (Nat × String)) :=
    if forbiddenWords.contains part then (line, part) :: found else found
  let (line, part, found) := code.foldl (init := (1, "", ([] : List (Nat × String))))
    fun (line, part, found) c =>
      if isWordChar c then
        (line, part.push c, found)
      else
        let found := flush line part found
        ((if c == '\n' then line + 1 else line), "", found)
  (flush line part found).reverse

/-- Each forbidden word that `source` uses as code, with the 1-based line it is on, in order. -/
def findForbidden (source : String) : List (Nat × String) :=
  forbiddenParts (blankProse source.toList .code [] ' ' [])

end Gate
