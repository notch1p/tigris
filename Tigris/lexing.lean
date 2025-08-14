import Tigris.parsing.types

infixr : 60 " <$ " => Functor.mapConst
infixr : 60 " $> " => flip Functor.mapConst

namespace Lexing open Parser Parser.Char

def alphanum' [Parser.Stream σ Char] [Parser.Error ε σ Char] [Monad m]
  : ParserT ε σ Char m Char :=
  withErrorMessage "expected letter or digit character or \'" do
    tokenFilter fun c => c.isAlphanum || c == '\'' || c == '_' || c == '·'
def alpha' [Parser.Stream σ Char] [Parser.Error ε σ Char] [Monad m]
  : ParserT ε σ Char m Char :=
  withErrorMessage "expected alphabetic character" do
    tokenFilter fun c => if c >= 'a' then c <= 'z' else c == '_' || c >= 'A' && c <= 'Z'
section
variable {σ}
def void : TParser σ β -> TParser σ Unit := (() <$ ·)

def MLCOMMENTL : TParser σ Unit := void $ string "(*"
def MLCOMMENTR : TParser σ Unit := void $ string "*)"

def comment : TParser σ Unit :=
  withBacktracking $
   (string "NB.") *> dropUntil (endOfInput <|> void eol) anyToken

def spaces : TParser σ Unit :=
  dropMany <| MLCOMMENTR <|> MLCOMMENTL <|> void ASCII.whitespace <|> comment <|> void eol

abbrev ws (t : TParser σ α) := spaces *> t <* spaces

def reservedOp := #["|", "->", ";;", "="]

def reserved :=
  #[ "infixl", "infixr", "match"
   , "data"  , "type"  , "with"
   , "else"  , "then"  , "let"
   , "rec"   , "fun"   , "fn"
   , "in"    , "if"]


def opLetters : List (TParser σ Char) :=
  [ '+', '-', '*', '/', ':', '$', '@', '%', '&'
  , '|', '<', '>', '=', '?', '!', '^', '.'].map $ char

open ASCII in private def ID' : TParser σ String :=
  withErrorMessage "identifier" do
      (· ++ ·)
  <$> (Char.toString <$> alpha')
  <*> foldl String.push "" alphanum'

def ID : TParser σ Symbol := do
  let id <- ID'
  if reserved.contains id then throwUnexpectedWithMessage none s!"expected identifier, not keyword {id}"
  else ws $ pure id

def intLit := @ASCII.parseInt
def strLit : TParser σ String :=
  char '"' *> foldl .push "" (tokenFilter (· != '"')) <* char '"'
def boolLit : TParser σ Bool := string "true" $> true <|> string "false" $> false

def isUpperInit (s : String) : Bool :=
  if h : s.atEnd 0 = true then false
  else (s.get' 0 h) >= 'A' && (s.get' 0 h) <= 'Z'

def between (l : Char) (t : TParser σ α) (r : Char) : TParser σ α :=
  ws (char l) *> t <* ws (char r)

def parenthesized (t : TParser σ α) : TParser σ α := between '(' t ')'

def kw (s : String) : TParser σ Unit := ws
                                    $ withBacktracking
                                    $ withErrorMessage "keyword"
                                    $ string s
                                    *> notFollowedBy alphanum'

def kwOp (s : String) : TParser σ Unit := ws
                                      $ withBacktracking
                                      $ withErrorMessage s!"end of {s}"
                                      $ string s
                                      *> notFollowedBy (first opLetters)


abbrev LET  : TParser σ Unit := kw "let"
abbrev IN   : TParser σ Unit := kw "in"
abbrev FUN  : TParser σ Unit := kw "fun"
abbrev IF   : TParser σ Unit := kw "if"
abbrev ELSE : TParser σ Unit := kw "else"
abbrev THEN : TParser σ Unit := kw "then"
abbrev REC  : TParser σ Unit := kw "rec"
abbrev MATCH: TParser σ Unit := kw "match"
abbrev WITH : TParser σ Unit := kw "with"
abbrev TYPE : TParser σ Unit := kw "type" <|> kw "data"

abbrev BAR  : TParser σ Unit := kwOp "|"
abbrev ARROW: TParser σ Unit := kwOp "=>" <|> kwOp "->"
abbrev COMMA: TParser σ Unit := kwOp ","
abbrev EQ   : TParser σ Unit := kwOp "="
abbrev END  : TParser σ Unit := kwOp ";;"
abbrev UNDERSCORE : TParser σ Unit
             := kwOp "_"

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
