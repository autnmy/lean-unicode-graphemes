/-!
# The forbidden-word rule

Project code may not use `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `extern` or
`unsafe`: each one either leaves a proof unfinished or lets code run that the kernel never checks.
A plain text search cannot enforce this, because the test files name these words in comments,
in strings and in «…» theorem names. `findForbidden` first blanks out that prose, then reports
each identifier part that equals a forbidden word.

What counts as prose: `--` comments, `/- … -/` comments (they nest, and doc comments are
included), character literals, the text of string literals, and «…» names. The `{…}` parts of
an interpolated string such as `s!"…"` or `m!"…"` hold Lean terms, so they are scanned as code.
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
  /-- Inside a character literal that starts with an escape, such as `'\n'`. -/
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

/-- `cs` with every prose character replaced by a space, built in reverse onto `out`.
`braces` has one entry for each open `{…}` part of an interpolated string: the number of `{`
opened inside that part that are still unclosed. `prev` is the last code character, used to tell
a character literal from the prime in a name like `h'`, and an interpolated string from a plain
one (`s!"`). -/
private def blankProse : List Char → Region → List Nat → Char → List Char → List Char
  | [], _, _, _, out => out.reverse
  | '-' :: '-' :: rest, .code, braces, _, out =>
    blankProse rest .lineComment braces ' ' (' ' :: ' ' :: out)
  | '/' :: '-' :: rest, .code, braces, _, out =>
    blankProse rest (.blockComment 1) braces ' ' (' ' :: ' ' :: out)
  | '"' :: rest, .code, braces, prev, out =>
    blankProse rest (.string (prev == '!')) braces ' ' (' ' :: out)
  | '«' :: rest, .code, braces, _, out =>
    blankProse rest .quotedName braces ' ' (' ' :: out)
  | '\'' :: rest, .code, braces, prev, out =>
    if isWordChar prev then
      blankProse rest .code braces '\'' ('\'' :: out)
    else
      -- The equation lets the termination proof see that `rest` is shorter in the last branch.
      match _h : rest with
      | '\\' :: afterEscape =>
        blankProse afterEscape .charLiteral braces ' ' (' ' :: ' ' :: out)
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
