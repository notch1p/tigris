import Tigris.parsing.types

infixr : 60 " <$ " => Functor.mapConst
infixr : 60 " $> " => flip Functor.mapConst

def String.isUpperInit (s : String) : Bool :=
  if h : s.atEnd 0 = true then false
  else (s.get' 0 h) >= 'A' && (s.get' 0 h) <= 'Z'
def String.isLowerInit (s : String) : Bool :=
  if h : s.atEnd 0 = true then false
  else (s.get' 0 h) >= 'a' && (s.get' 0 h) <= 'z'

namespace Lexing open Parser Parser.Char

def alphanum' [Parser.Stream σ Char] [Parser.Error ε σ Char] [Monad m]
  : ParserT ε σ Char m Char :=
  withErrorMessage "letter or digit character or \'" do
    tokenFilter fun c => c.isAlphanum || c == '\'' || c == '_' || c == '!' || c == '?'
def alpha' [Parser.Stream σ Char] [Parser.Error ε σ Char] [Monad m]
  : ParserT ε σ Char m Char :=
  withErrorMessage "alphabetic character" do
    tokenFilter fun c => if c >= 'a' then c <= 'z' else c == '_' || c >= 'A' && c <= 'Z'
section
variable {σ}
def void : TParser σ β -> TParser σ Unit := (() <$ ·)

def MLCOMMENTL : TParser σ Unit := void $ string "(*"
def MLCOMMENTR : TParser σ Unit := void $ string "*)"

def comment : TParser σ Unit :=
  withBacktracking $
   (string "NB." <|> string "--") *> dropUntil (endOfInput <|> void eol) anyToken

def spaces : TParser σ Unit :=
  dropMany <| MLCOMMENTR <|> MLCOMMENTL <|> void ASCII.whitespace <|> comment <|> void eol

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
   , "instance", "else"  , "then"  , "let"
   , "and"     , "rec"   , "fun"
   , "fn"      , "in"    , "if"]

open ASCII in private def ID' : TParser σ String :=
  withErrorMessage "identifier" do
      (· ++ ·)
  <$> (Char.toString <$> alpha')
  <*> foldl String.push "" alphanum'

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

def kw (s : String) : TParser σ Unit := spaces *>
                                     (withBacktracking
                                    $ withErrorMessage s!"kw '{s}'"
                                    $ string s
                                    *> notFollowedBy alphanum')

def kwOpExact (s : String) : TParser σ Unit := spaces *>
   (withBacktracking
  $ withErrorMessage s!"kwOp '{s}'"
  $ void
  $ string s)

def kwOpNoExtend (s : String) (badNext : Char -> Bool) : TParser σ Unit := spaces *>
   (withBacktracking
  $ withErrorMessage s!"kwOp '{s}'"
  $ string s *> notFollowedBy (tokenFilter badNext))
abbrev LET    : TParser σ Unit := kw "let"
abbrev IN     : TParser σ Unit := kw "in"
abbrev FUN    : TParser σ Unit := kw "fun"
abbrev IF     : TParser σ Unit := kw "if"
abbrev ELSE   : TParser σ Unit := kw "else"
abbrev THEN   : TParser σ Unit := kw "then"
abbrev REC    : TParser σ Unit := kw "rec"
abbrev MATCH  : TParser σ Unit := kw "match"
abbrev WITH   : TParser σ Unit := kw "with"
abbrev TYPE   : TParser σ Unit := kw "type" <|> kw "data"
abbrev MUTUAL : TParser σ Unit := kw "mutual"
abbrev AND    : TParser σ Unit := kw "and"
abbrev FORALL : TParser σ Unit := kw "forall"
abbrev FORALL' : TParser σ Unit := spaces *>
                                    ( withBacktracking
                                    $ withErrorMessage s!"kw '∀'"
                                    $ void
                                    $ string "∀")
abbrev EXTERN : TParser σ Unit := kw "extern"
abbrev CLASS : TParser σ Unit := kw "class"
abbrev INSTANCE : TParser σ Unit := kw "instance"

abbrev TYPE? : TParser σ Bool := do
  if <- test TYPE then return false
  else if <- test CLASS then return true
  else throwUnexpected

abbrev BAR  : TParser σ Unit := kwOpNoExtend "|" (· == '|')
abbrev ARROW: TParser σ Unit := spaces *>
   (withBacktracking
  $ withErrorMessage "reserved operator '=>' or '->'"
  $ (void $ string "=>") <|> (void $ string "->"))
abbrev COMMA: TParser σ Unit := kwOpExact ","
abbrev EQ   : TParser σ Unit := kwOpNoExtend "=" (fun c => c == '>' || c == '=')
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
