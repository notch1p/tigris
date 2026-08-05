import Tigris.TCNF.nf

namespace TCNF.Interpreter open Std TCNF open MLType (TypingError)

inductive Value where
  | int (i : Int) | bool (b : Bool) | str (s : String) | unit
  | pair (p q : Value)
  | constr (tag : Tag) : Array Value -> Value
  | clos (codeptr : FVarId) : Array Value -> Value
deriving Repr, Inhabited

def Value.beq : Value -> Value -> Bool
  | .int i, .int j => i == j
  | .bool b, .bool b' => b == b'
  | .str s, .str s' => s == s'
  | .unit, .unit => true
  | .constr t as, .constr t' as' => t == t' && arrayEqv as as'
  | .clos c _, .clos c' _ => c == c'
  | _, _ => false
where
  arrayEqv xs ys :=
    if h : xs.size = ys.size then go xs.size xs ys h Nat.le.refl
    else false
  go i xs ys (h : xs.size = ys.size) (h' : i <= xs.size) :=
    match H : i with
    | 0      => true
    | i' + 1 => beq xs[i'] ys[i']

instance : BEq Value := ⟨Value.beq⟩
abbrev Frame := TreeMap FVarId Value
abbrev Externs := Lean.Data.Trie Nat
structure IState where
  globaldecls : HashMap FVarId $ Decl .postCC := ∅
  topvals     : HashMap FVarId Value := ∅
  locals      : Frame := ∅
                              --   params          body      captured
  joins       : TreeMap FVarId (Array FVarId × Code .postCC × Frame)
              := ∅
deriving Inhabited

def externTab : Externs := .ofList $
  [ ("%println"      , 1)
  , ("%to-string"    , 2)
  , ("%string-append", 3)
  , ("%read"         , 4)]

abbrev EvaluatorM := ReaderT IState $ EIO TypingError

open Lexing in partial def parseValue : TParser σ Value := Parser.first $
  [ parseInt
  , parseStr
  , parseBool
  , parseProd ]
where
  parseInt  : TParser σ Value := dumbspaces *> intLit <&> .int
  parseStr  : TParser σ Value := dumbspaces *> strLit <&> .str
  parseBool : TParser σ Value :=
    dumbspaces *> (Parser.Char.string "true" <|> Parser.Char.string "false") >>=
      fun | "true"  => return .bool true
          | "false" => return .bool false
          | _       => Parser.throwUnexpected

  parseProd : TParser σ Value  := parenthesized do
    let es <- dumbspaces *> Parser.sepBy COMMA parseValue
    match h : es.size with
    | 0 => return .unit
    | 1 => return es[0]
    | _ + 2 => return es[0:es.size - 1].foldr Value.pair es.back

in def readValue (s : String) : EvaluatorM Value :=
  match runST fun _ => parseValue <* spaces <* Parser.endOfInput |>.run s |>.run' ({}, "")
  with
  | .ok _ t    => pure t
  | .error _ e => throw $ .Lowlevel $ toString $ e

open TCNF.PP (comma) in
def Value.toFormat : Value -> Format
  | .unit => "()"
  | .int i => format i
  | .bool b => format b | .str s => repr s
  | .constr t fs =>
    let s := if fs.isEmpty then .nil else .nestD .line ++ .bracket "⟨" (.joinSep' (fs.map toFormat) PP.comma) "⟩"
    .group $ t ++ s
  | .clos fid fs =>
    let s := if fs.isEmpty then .nil else .nestD $ .line ++ .sbracket (.joinSep' (fs.map toFormat) PP.comma)
    .bracket "#<" ("FUNCTION" <> format fid ++ s) ">"
  | p => .paren $ joinSepR (collectPair p []) -- very awkward structural recursion
where
  collectPair : Value -> List Format -> List Format
  | .pair a b   , acc => collectPair b (toFormat a :: acc)
  | .unit       , acc => "()" :: acc
  | .int i      , acc => format i :: acc
  | .bool b     , acc => format b :: acc
  | .str s      , acc => repr s :: acc
  | .constr t fs, acc =>
    let s := if fs.isEmpty then .nil else .nestD $ .line ++ .bracket "⟨" (.joinSep' (fs.map toFormat) PP.comma) "⟩"
    .group (t ++ s) :: acc
  | .clos fid fs, acc =>
    let s := if fs.isEmpty then .nil else .nestD $ .line ++ .sbracket (.joinSep' (fs.map toFormat) PP.comma)
    .bracket "#<" ("FUNCTION" <> format fid ++ s) ">" :: acc
  joinSepR (xs : List Format) : Format :=
    if h : xs = [] then .nil
    else List.foldl1 (fun acc s => s ++ comma ++ acc) xs h
instance : ToFormat Value := ⟨Value.toFormat⟩
instance : ToString Value := ⟨Format.pretty ∘ Value.toFormat⟩

def _root_.Nat.countDigits n := howmanydigits n 0 -- n must > 0
where howmanydigits n acc :=
  if h : n = 0
  then acc
  else howmanydigits (n / 10) (acc + 1)

section open PrettyPrint
abbrev FrameHeader
  : List Text.SString := ["FVar", "Value"].map fun s => ⟨s, {style := [.bold]}⟩
abbrev alignH : Align FrameHeader := (.right, .left)
def frameTable (st : Frame) (h : st.isEmpty = false) : TableOf FrameHeader :=
  let width := st.maxKey h |>.countDigits |> max 4 -- |"FVar"| = 4
  .mk $
    st.foldl (init := #[]) fun t k v =>                       -- column margin = 3
      t.push (.str $ toString k, .str $ Format.pretty (indent := 3 + 3 + width) (column := 3 + 3 + width) $ format v)
def frameString f h := frameTable f h
                    |> tabulate "\nCurrent Frame:" {align := alignH, divider? := false}
end

scoped macro "impossible!" v:interpolatedStr(term) : term =>
  ``(throw $ TypingError.Lowlevel $ "Interpreter: " ++ s! $v)

/-- any error tagged Lowlevel should be (but isn't) caught by a previous pass
   e.g. typechecker
-/
scoped macro "impossibleF!" v:interpolatedStr(term) : term =>
  `(read >>= fun is =>
     match is with
     | {locals,..} =>
       if h : TreeMap.isEmpty locals then impossible! $v
       else
         throw $ TypingError.Lowlevel
               $ "Interpreter: " ++ s! $v
              ++ frameString locals (eq_false_of_ne_true h))

scoped macro "applyHBinOp!" t:ident as:ident key1:ident key2:ident node:ident : term =>
  ``($key1 $as[0] >>= fun i =>
      $key2 $as[1] >>= fun j =>
        pure ($node ($t i j)))

scoped macro "applyBinOp!" t:ident as:ident key:ident node:ident : term =>
  ``(applyHBinOp! $t $as $key $key $node)

instance : Coe Int Value    := ⟨.int⟩
instance : Coe Bool Value   := ⟨.bool⟩
instance : Coe String Value := ⟨.str⟩
instance : Coe Unit Value   := ⟨fun _ => .unit⟩
scoped instance : MonadLift IO EvaluatorM
  := ⟨liftM ∘ EIO.adapt TypingError.Lowlevel ∘ liftEIO⟩

@[inline]
def expectInt : Value -> EvaluatorM Int
  | .int i => return i
  | v => impossibleF! "expected Int, found {v}"
def expectBool : Value -> EvaluatorM Bool
  | .bool b => return b
  | v => impossibleF! "expected Bool, found {v}"
def expectStr : Value -> EvaluatorM String
  | .str s => return s
  | v => impossibleF! "expected String, found {v}"
