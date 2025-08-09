import Tigris.parsing.types

infixr : 60 " <$ " => Functor.mapConst
infixr : 60 " $> " => flip Functor.mapConst

namespace Lexing open Parser Parser.Char

def INT := @ASCII.parseInt

def alphanum' [Parser.Stream σ Char] [Parser.Error ε σ Char] [Monad m]
  : ParserT ε σ Char m Char :=
  withErrorMessage "expected letter or digit character or \'" do
    tokenFilter fun c => c.isAlphanum || c == '\'' || c == '_'
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

def reserved := 
  #[ "infixl", "infixr", "match"
   , "data"  , "type"  , "with"
   , "let"   , "rec"   , "in"
   , "fn"    , "fun"   , "="
   , "if"    , "else"  , "then"
   , "|"     , "->"    , ";;"]

open ASCII in def ID' : TParser String :=
  withErrorMessage "identifier" do
      (· ++ ·)
  <$> (Char.toString <$> alpha')
  <*> foldl String.push "" alphanum'

def ID : TParser Symbol := do
  let id <- ID'
  if reserved.contains id then throwUnexpectedWithMessage none s!"expected identifier, not keyword {id}"
  else ws $ pure id

def isUpperInit (s : String) : Bool :=
  if h : s.atEnd 0 = true then false
  else (s.get' 0 h) >= 'A' && (s.get' 0 h) <= 'Z'

def between (l : Char) (t : TParser α) (r : Char) : TParser α :=
  ws (char l) *> t <* ws (char r)

def parenthesized (t : TParser α) : TParser α := between '(' t ')'

abbrev kw (s : String) : TParser Unit := ws 
                                         $ withBacktracking
                                         $ withErrorMessage "keyword"
                                         $ string s
                                         *> notFollowedBy alphanum'

abbrev LET   := kw "let"
abbrev IN    := kw "in"
abbrev FUN   := kw "fun"
abbrev EQ    := kw "="
abbrev IF    := kw "if"
abbrev ELSE  := kw "else"
abbrev THEN  := kw "then"
abbrev ARROW := kw "->"
abbrev COMMA := kw ","
abbrev REC   := kw "rec"
abbrev END   := kw ";;"
abbrev MATCH := kw "match"
abbrev WITH  := kw "with"
abbrev BAR   := kw "|"
abbrev TYPE  := kw "type"
abbrev DATA  := kw "DATA"

abbrev ADD   := "+"
abbrev SUB   := "-"
abbrev MUL   := "*"
abbrev DIV   := "/"
abbrev DOL   := "$"
abbrev ATT   := "@@"

abbrev INFIXL := kw "infixl"
abbrev INFIXR := kw "infixr"

end Lexing
