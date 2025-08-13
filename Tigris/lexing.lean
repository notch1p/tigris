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

def void : TParser α -> TParser Unit := (() <$ ·)

def MLCOMMENTL := void $ string "(*"
def MLCOMMENTR := void $ string "*)"

def comment : TParser Unit :=
  withBacktracking $
   (string "NB.") *> dropUntil (endOfInput <|> void eol) anyToken

def spaces : TParser Unit :=
  dropMany <| MLCOMMENTR <|> MLCOMMENTL <|> void ASCII.whitespace <|> comment <|> void eol

abbrev ws (t : TParser α) := spaces *> t <* spaces

def reservedOp := #["|", "->", ";;", "="]

def reserved :=
  #[ "infixl", "infixr", "match"
   , "data"  , "type"  , "with"
   , "else"  , "then"  , "let"
   , "rec"   , "fun"   , "fn"
   , "in"    , "if"]


def opLetters : List (TParser Char) :=
  [ '+', '-', '*', '/', ':', '$', '@', '%', '&'
  , '|', '<', '>', '=', '?', '!', '^', '.'].map $ char

open ASCII in private def ID' : TParser String :=
  withErrorMessage "identifier" do
      (· ++ ·)
  <$> (Char.toString <$> alpha')
  <*> foldl String.push "" alphanum'

def ID : TParser Symbol := do
  let id <- ID'
  if reserved.contains id then throwUnexpectedWithMessage none s!"expected identifier, not keyword {id}"
  else ws $ pure id

def intLit := @ASCII.parseInt
def strLit : TParser String :=
  char '"' *> foldl .push "" (tokenFilter (· != '"')) <* char '"'
def boolLit : TParser Bool := string "true" $> true <|> string "false" $> false

def isUpperInit (s : String) : Bool :=
  if h : s.atEnd 0 = true then false
  else (s.get' 0 h) >= 'A' && (s.get' 0 h) <= 'Z'

def between (l : Char) (t : TParser α) (r : Char) : TParser α :=
  ws (char l) *> t <* ws (char r)

def parenthesized (t : TParser α) : TParser α := between '(' t ')'

def kw (s : String) : TParser Unit := ws
                                    $ withBacktracking
                                    $ withErrorMessage "keyword"
                                    $ string s
                                    *> notFollowedBy alphanum'

def kwOp (s : String) : TParser Unit := ws
                                      $ withBacktracking
                                      $ withErrorMessage s!"end of {s}"
                                      $ string s
                                      *> notFollowedBy (first opLetters)


abbrev LET   := kw "let"
abbrev IN    := kw "in"
abbrev FUN   := kw "fun"
abbrev IF    := kw "if"
abbrev ELSE  := kw "else"
abbrev THEN  := kw "then"
abbrev REC   := kw "rec"
abbrev MATCH := kw "match"
abbrev WITH  := kw "with"
abbrev TYPE  := kw "type" <|> kw "data"

abbrev BAR   := kwOp "|"
abbrev ARROW := kwOp "=>" <|> kwOp "->"
abbrev COMMA := kwOp ","
abbrev EQ    := kwOp "="
abbrev END   := kwOp ";;"
abbrev UNDERSCORE
             := kwOp "_"

abbrev ADD   := "+"
abbrev SUB   := "-"
abbrev MUL   := "*"
abbrev DIV   := "/"
abbrev DOL   := "$"
abbrev ATT   := "@@"

abbrev INFIXL := kw "infixl"
abbrev INFIXR := kw "infixr"

end Lexing
