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

structure IState where
  globaldecls : TreeMap FVarId $ Decl .postCC := ∅
  topvals     : TreeMap FVarId Value := ∅
  locals      : TreeMap FVarId Value := ∅
                              --   params          body         captured locals
  joins       : TreeMap FVarId (Array FVarId × Code .postCC × TreeMap FVarId Value)
              := ∅
deriving Inhabited

abbrev EvaluatorM := ReaderT IState $ EIO TypingError

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

/-- any error tagged Lowlevel should be (but isn't) caught by a previous pass
   e.g. typechecker
-/
scoped macro "impossible!" v:interpolatedStr(term) : term =>
  ``(throw $ TypingError.Lowlevel $ "Interpreter: " ++ s! $v)

scoped macro "applyBinOp!" t:ident as:ident key:ident node:ident : term =>
  ``($key $as[0] >>= fun i =>
      $key $as[1] >>= fun j =>
        pure ($node ($t i j)))

instance : Coe Int Value    := ⟨.int⟩
instance : Coe Bool Value   := ⟨.bool⟩
instance : Coe String Value := ⟨.str⟩
instance : Coe Unit Value   := ⟨fun _ => .unit⟩

@[inline]
def expectInt : Value -> EvaluatorM Int
  | .int i => return i
  | v => impossible! "expected Int, found {v}"
def expectBool : Value -> EvaluatorM Bool
  | .bool b => return b
  | v => impossible! "expected Bool, found {v}"
def expectStr : Value -> EvaluatorM String
  | .str s => return s
  | v => impossible! "expected String, found {v}"
