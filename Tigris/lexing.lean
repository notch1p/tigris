import Tigris.parsing.types

infixr : 60 " <$ " => Functor.mapConst
infixr : 60 " $> " => flip Functor.mapConst

def List.isSubsingleton : List α -> Bool
  | _ :: _ :: _ => false
  | _ => true

def String.isUpperInit (s : String) : Bool :=
  if h : s.atEnd 0 = true then false
  else (s.get' 0 h) >= 'A' && (s.get' 0 h) <= 'Z'
def String.isLowerInit (s : String) : Bool :=
  if h : s.atEnd 0 = true then false
  else (s.get' 0 h) >= 'a' && (s.get' 0 h) <= 'z'
@[inline] def Function.on (g : β -> β -> γ) (f : α -> β)
  : α -> α -> γ := fun x y => g (f x) (f y)

namespace Lexing open Parser Parser.Char

def alphanum' [Parser.Stream σ Char] [Parser.Error ε σ Char] [Monad m]
  : ParserT ε σ Char m Char :=
  withErrorMessage "letter or digit character or \'" do
    tokenFilter fun c => c.isAlphanum || c == '\'' || c == '_' || c == '!' || c == '?'
def alpha' [Parser.Stream σ Char] [Parser.Error ε σ Char] [Monad m]
  : ParserT ε σ Char m Char :=
  withErrorMessage "alphabetic character" do
    tokenFilter fun c => if c >= 'a' then c <= 'z' else c == '_' || c >= 'A' && c <= 'Z'
def lowercase' [Parser.Stream σ Char] [Parser.Error ε σ Char] [Monad m]
  : ParserT ε σ Char m Char :=
  withErrorMessage "alphabetic lowercase character" do
    tokenFilter fun c => if c >= 'a' then c <= 'z' else c == '_'
def oneOf [Parser.Stream σ Char] [Parser.Error ε σ Char] [Monad m] (l : List Char)
  : ParserT ε σ Char m Char := withBacktracking $ withErrorMessage s!"expected one of {l}" $ tokenFilter (· ∈ l)

section
variable {σ}
def void : TParser σ β -> TParser σ Unit := (() <$ ·)

def MLCOMMENTL : TParser σ Unit := void $ string "(*"
def MLCOMMENTR : TParser σ Unit := void $ string "*)"

def eol : TParser σ Char := withErrorMessage "expected newline" do
    let c <- (ASCII.cr *> ASCII.lf) <|> ASCII.lf
    let pos <- getPosition
    modify fun (pe, l) => ({pe with lastEol := pos.byteIdx},l)
    return c

/-- does NOT consume eol -/
def comment : TParser σ Unit :=
  withBacktracking $
   (string "NB." <|> string "--") *> dropUntil (endOfInput <|> void (lookAhead eol)) anyToken

def hspaces : TParser σ Unit :=
  dropMany <| MLCOMMENTR
          <|> MLCOMMENTL
          <|> (void $ tokenFilter fun c => c == ' ' || c == '\t')
          <|> comment

def eol1 : TParser σ Unit := void eol

partial def vspaces : TParser σ Unit :=
  hspaces *> eol *> go where go := do if <- test (hspaces *> eol1) then go

/--
count (AND consume) consecutive leading spaces/tabs.
Never fails.
-/
@[inline] partial def indentCol : TParser σ Nat := go 0 where
  go n :=
    option? (oneOf [' ', '\t']) >>= fun
    | some ' '  => go (n + 1)
    | some '\t' => go (n + tabWidth)
    | _         => pure n

/--
test if the current indentation `col` (from `indentCol`) satisfies
- `col · ref` where `·` is one of `> >= ==`.
- otherwise backtracks the same amount that indentCol consumed.
-/
def indentGuard
  (cmp : Nat -> Nat -> Bool) (rel : String) (ref : Nat)
  : TParser σ Unit := withBacktracking do
  let col <- indentCol
  if cmp col ref then return ()
  else
    throwUnexpectedWithMessage none
      s!"indentation mismatch: got {col}, expected indentation {rel} {ref}"

def colGt (n : Nat) : TParser σ Unit := indentGuard (· > ·) ">" n
def colGe (n : Nat) : TParser σ Unit := indentGuard (· >= ·) ">=" n
def colEq (n : Nat) : TParser σ Unit := indentGuard (· == ·) "==" n
def currentCol : TParser σ Nat :=
  get <&> fun ({indentStack,..}, _) => indentStack.headD 0

/-- column with respect to current line start-/
def currentColAbs : TParser σ Nat :=
  get >>= fun ({lastEol,..}, _) =>
    getPosition <&> fun ⟨byteIdx⟩ => byteIdx - lastEol

def pushCol (n : Nat) : TParser σ Unit :=
  modify fun (pe, log) =>
    ({pe with indentStack := n :: pe.indentStack}, log)
def colGtCur : TParser σ Unit := colGt =<< currentCol
def colGeCur : TParser σ Unit := colGe =<< currentCol
def colEqCur : TParser σ Unit := colEq =<< currentCol
def popCol : TParser σ Unit := modify
  fun (pe, log) => ({pe with indentStack := pe.indentStack.tail}, log)

attribute [inline]
  colGt colGe colEq
  colGtCur colGeCur colEqCur
  pushCol currentCol popCol

/--
helper combinator used by `spaces`.
Parses consecutive blank lines conditionally (described below).
Consider

```lean4
let rec x = y where
  y = f a
  z = g b
```
To prevent greedy funapp parsing of `y := (= (f a z) (g b))` and instead
parse as two items,
- Inside a layout block,
  only consume a line if `col > base` (i.e. indented).
  This permits (but not w/o the indentation)

```lean4
    where
      y = f
        a
  --  ^^ indented, parse as funapp
```

- otherwise, fail and fallback to caller, which tries layout parsing.
-/
def crossLine : TParser σ Unit := withBacktracking do
  eol1
  dropMany $ hspaces *> eol1
  let ({indentStack,..}, _) <- get
  if !indentStack.isSubsingleton then
    let base := indentStack.headD 0
    let col <- lookAhead indentCol
    if col > base then return ()
    else throwUnexpectedWithMessage none s!"dedent: col {col} <= baseline {base}"

/--
only consumes newline if `crossLine` permits it.
Note that crossLine itself already consumes consecutive blank lines if it succeeds.
-/
partial def spaces : TParser σ Unit := do
  hspaces
  if <- test crossLine then spaces

/--
Does not check `crossLine`. Useful for keywords.
-/
partial def dumbspaces : TParser σ Unit := do
  hspaces
  if <- test eol1 then dumbspaces

/--
After a linebreak,
measure and consume the indentation on the next line, then run `p baseline`.
-/
def withBaseline (p : Nat -> TParser σ α) : TParser σ α := vspaces *> indentCol >>= p

/--
Enter a new layout block after a linebreak.
- Require the next line's indentation to be strictly greater than the current baseline (strict=true),
  or ≥ current baseline (strict=false).
- Push that indentation as the new baseline while parsing `p`.
- Pop it afterwards.
-/
def withBlock (strict : Bool) (p : TParser σ α) : TParser σ α := do
  vspaces
  let base <- indentCol
  let cur  <- currentCol
  if strict then
    if base <= cur then
      error s!"expected indentation > {cur} to start a block, got {base}"
      throwUnexpected
  else
    if base < cur then
      error s!"expected indentation >= {cur} to start a block, got {base}"
      throwUnexpected
  pushCol base
  try
    let r <- p
    popCol
    return r
  catch e => popCol; throw e

/--
Enter a layout block whose baseline is `col`, without consuming a linebreak.
Use when the first item already sits on the current line and its column
should be the alignment baseline for any continuation lines.
-/
def withInlineBlock (col : Nat) (p : TParser σ α) : TParser σ α := do
  pushCol col
  try
    let r <- p
    popCol
    return r
  catch e => popCol; throw e

abbrev ws (t : TParser σ α) := spaces *> t <* spaces

def reservedOp : Lean.Data.Trie Symbol := .ofList
  [ ("|", "|")
  , ("->", "->")
  , (";;", ";;")
  , ("=>", "=>")
  , (",", ",")
  , ("_", "_")
  , (":", ":")
  , ("∀", "∀")]

def reserved :=
  #[ "mutual"  ,"infixl" , "infixr", "match", "extern"
   , "class"   , "forall", "data"  , "type"  , "with"
   , "instance", "else"  , "then"  , "let", "prefix", "postfix"
   , "and"     , "rec"   , "fun"
   , "fn"      , "in"    , "if"    , "where"]

open ASCII in private def ID' : TParser σ String :=
  withErrorMessage "identifier" do
      (· ++ ·)
  <$> (Char.toString <$> alpha')
  <*> foldl String.push "" alphanum'

open ASCII in private def IDlower' : TParser σ String :=
  withErrorMessage "lowercase identifier" do
      (· ++ ·)
  <$> (Char.toString <$> lowercase')
  <*> foldl String.push "" alphanum'

def IDlower : TParser σ Symbol := do
  let id <- spaces *> IDlower'
  if reserved.contains id then throwUnexpectedWithMessage none s!"expected identifier, not keyword '{id}'"
  pure id

def ID : TParser σ Symbol := do
  let id <- spaces *> ID'
  if reserved.contains id then throwUnexpectedWithMessage none s!"expected identifier, not keyword '{id}'"
  pure id

def intLit := @ASCII.parseInt
def strLit : TParser σ String :=
  char '"' *> foldl .push "" (tokenFilter (· != '"')) <* char '"'
def boolLit : TParser σ Bool := string "true" $> true <|> string "false" $> false

def between (l : Char) (t : TParser σ α) (r : Char) : TParser σ α :=
  (ws $ char l) *> t <* (ws $ char r)

def parenthesized (t : TParser σ α) : TParser σ α := between '(' t ')'
def braced (t : TParser σ α) : TParser σ α := between '{' t '}'
def sbrack (t : TParser σ α) : TParser σ α := between '[' t ']'

def kw (s : String) : TParser σ Unit := dumbspaces *>
                                     (withBacktracking
                                    $ withErrorMessage s!"kw '{s}'"
                                    $ string s
                                    *> notFollowedBy alphanum')

def kwOpExact (s : String) : TParser σ Unit := dumbspaces *>
  ( withBacktracking
  $ withErrorMessage s!"kwOp '{s}'"
  $ void
  $ string s)
def kwOpNoExtend (s : String) (badNext : Char -> Bool) : TParser σ Unit := dumbspaces *>
  ( withBacktracking
  $ withErrorMessage s!"kwOp '{s}'"
  $ string s *> notFollowedBy (tokenFilter badNext))

/--
Parse 1+ items, separated by either:
- `;` (on the current line, optionally followed by a layout step to an
  aligned next line), or
- an aligned newline alone (next non-blank line indented exactly to
  `baseline`).

Backtrackes if neither.

Note: Use `aligned1` in the current block.
-/
def alignedMany1 (baseline : Nat) (item : TParser σ α) : TParser σ (Array α) :=
  item >>= fun init =>
    foldl Array.push #[init] $ sepStep *> item
where
  sepStep : TParser σ Unit := first $
    [ (SEMICOLON <|> AND) <* hspaces <* optional (vspaces *> colEq baseline)
    , vspaces *> colEq baseline]
  SEMICOLON := kwOpExact ";"
  AND       := kw "and"

def aligned1 (p : TParser σ α) : TParser σ (Array α) :=
  alignedMany1 (item := p) =<< currentCol

abbrev LET      : TParser σ Unit := kw "let"
abbrev IN       : TParser σ Unit := kw "in"
abbrev FUN      : TParser σ Unit := kw "fun"
abbrev IF       : TParser σ Unit := kw "if"
abbrev ELSE     : TParser σ Unit := kw "else"
abbrev THEN     : TParser σ Unit := kw "then"
abbrev REC      : TParser σ Unit := kw "rec"
abbrev MATCH    : TParser σ Unit := kw "match"
abbrev WITH     : TParser σ Unit := kw "with"
abbrev TYPE     : TParser σ Unit := kw "type" <|> kw "data"
abbrev MUTUAL   : TParser σ Unit := kw "mutual"
abbrev AND                       := @alignedMany1.AND
abbrev POSTFIX  : TParser σ Unit := kw "postfix"
abbrev PREFIX   : TParser σ Unit := kw "prefix"
abbrev FORALL   : TParser σ Unit := kw "forall"
abbrev WHERE    : TParser σ Unit := kw "where"
abbrev FORALL'  : TParser σ Unit := spaces *>
                                     ( withBacktracking
                                     $ withErrorMessage s!"kw '∀'"
                                     $ void
                                     $ string "∀")
abbrev EXTERN   : TParser σ Unit := kw "extern"
abbrev CLASS    : TParser σ Unit := kw "class"
abbrev INSTANCE : TParser σ Unit := kw "instance"
abbrev SEMICOLON := @alignedMany1.SEMICOLON

abbrev TYPE? : TParser σ Bool := do
  if <- test TYPE then return false
  else if <- test CLASS then return true
  else throwUnexpected

abbrev BAR  : TParser σ Unit := kwOpNoExtend "|" (· == '|')
abbrev ARROW: TParser σ Unit := spaces *>
  ( withBacktracking
  $ withErrorMessage "reserved operator '=>' or '->'"
  $ (void $ string "=>") <|> (void $ string "->"))
abbrev COMMA: TParser σ Unit := kwOpExact ","
abbrev EQ   : TParser σ Unit := kwOpExact ":=" <|> kwOpNoExtend "=" (fun c => c == '>' || c == '=')
abbrev END  : TParser σ Unit := kwOpExact ";;"
abbrev COLON: TParser σ Unit := kwOpExact ":"
abbrev UNDERSCORE : TParser σ Unit := kwOpExact "_"

abbrev ADD   := "+"
abbrev SUB   := "-"
abbrev MUL   := "*"
abbrev DIV   := "/"
abbrev DOL   := "$"
abbrev ATT   := "@@"

abbrev INFIXL : TParser σ Unit := kw "infixl"
abbrev INFIXR : TParser σ Unit := kw "infixr"
end

end Lexing

namespace Parsing open Lexing Parser

def alignedBindings (bindingParser : TParser σ α) : TParser σ $ Array α :=
  hspaces *> option? (lookAhead eol1) >>=
    fun
    | some _ => withBlock true $ aligned1 bindingParser -- block layout
                -- inline block/ sepBy `;`/`and` (same semantics)
    | none   => withInlineBlock (p := aligned1 bindingParser) =<< currentColAbs

@[inline]
def whereBindings (bindingParser : TParser σ α) : TParser σ $ Array α :=
  WHERE *> alignedBindings bindingParser

/--
- Parse 1+ BARs
- each BAR has its own layout
  i.e. BAR's column is locally (within the branch)
  the new baseline.

This way, the branch body can
dedent below the surrounding binding's baseline without
being parsed as an layout block ending.
- as long as it stays strictly indented past the BAR itself.

A practical problem this addresses is when mixing
matching branches with `Lexing.crossLine`. Consider (applies to let block aswell)

```lean4
let rec x = 1
where f -- this style of not aligning BARs to `f` is common for large codes
  | 0 => e
  | 1 =>
    e -- must be indented past `f` if not for the local baseline override.
      -- this it expected because of the restriction `crossLine` imposes.

      g := ... -- more bindings
```

If there were more bindings after `f`,
such as the `g` shown here, then this would be a parse error
since it is within the local layout of the second branch.
This should match Lean's behavior and `f`'s body must be
aligned or indented past `f` for `g` to be parsed.

- Note that BARs aren't required to align nor relevant here, currently.
-/
def barBranches (branchParser : TParser σ α) : TParser σ $ Array α :=
  takeMany1 do
    dumbspaces
    let col <- currentColAbs
    BAR
    withInlineBlock col branchParser

end Parsing
