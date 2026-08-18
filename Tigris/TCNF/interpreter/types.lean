import Tigris.TCNF.nf

namespace TCNF.Interpreter open Std TCNF open MLType (TypingError)

inductive Value where
  | int (i : Int) | bool (b : Bool) | str (s : String) | unit
  | pair (p q : Value)
  | constr (tag : Tag) : Array Value -> Value
  | clos (codeptr : FVarId) : Array Value -> Value
deriving Repr, Inhabited

unsafe def Value.ptrEqV : Value -> Value -> Bool
  | .int i, .int j => ptrEq i j || i == j   -- GMP Int. not always unboxed
  | .bool b, bool b' => b == b'
  | .str s, .str s' => ptrEq s s' || s == s'
  | .unit, .unit => true
  | .constr t as, .constr t' as' => (ptrEq t t' || t == t') && arrayEqv as as'
  | .clos c _, .clos c' _ => ptrEq c c' || c == c'
  | .pair p q, .pair p' q' => (ptrEq p p' || p.ptrEqV p') && (ptrEq q q' || q.ptrEqV q')
  | _, _ => false
where
  arrayEqv xs ys := -- array can't be shared so do not ptrEq on array.
    if h : xs.size = ys.size then go xs.size xs ys h Nat.le.refl
    else false
  go i xs ys (h : xs.size = ys.size) (h' : i <= xs.size) :=
    match H : i with
    | 0      => true
    | i' + 1 => ptrEqV xs[i'] ys[i']

@[implemented_by ptrEqV] def Value.beq : Value -> Value -> Bool
  | .int i, .int j => i == j
  | .bool b, .bool b' => b == b'
  | .str s, .str s' => s == s'
  | .unit, .unit => true
  | .constr t as, .constr t' as' => t == t' && arrayEqv as as'
  | .clos c _, .clos c' _  => c == c'
  | .pair p q, .pair p' q' => p.beq p' && q.beq q'
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

inductive Kont where
  | halt
  | letK (fv : FVarId) (rest : Code .postCC) (env : Frame) (k : Kont)
  | appK (codeptr : FVarId) (caputred : Array Value) (remaining : Subarray Value) (k : Kont)


abbrev EvaluatorCEK := EvaluatorM
--instance : MonadLift EvaluatorM EvaluatorCEK := ⟨(· ·.toIState)⟩

def Kont.trace (kont : Kont) : EvaluatorCEK String := go kont "\nBacktrace:" where
  go
  | .halt, acc => return acc
  | .letK fv _ env k, acc => fun s@{globaldecls, ..} =>
    let name := globaldecls[fv]?.elim s!"#{fv}" fun {name,..} => name
    go k (acc ++ s!"\n  let {name} (env size : {env.size})") s
  | .appK c _ rem k, acc => fun s@{globaldecls,..} =>
    let name := globaldecls[c]?.elim s!"#{c}" fun {name,..} => name
    go k (acc ++ s!"\n  #<FUNCTION {name}> ({rem.size} remaining args)") s


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

in def readValue (s : String) : EvaluatorCEK Value :=
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

@[inline] def throwErr (s : String) : EIO TypingError α :=
  throw $ TypingError.Lowlevel $ "Interpreter: " ++ s
def throwErrWithFrame (s : String) : EvaluatorCEK α := fun {locals,..} =>
  if h : TreeMap.isEmpty locals
  then throwErr s
  else throw $ TypingError.Lowlevel
             $ "Interpreter: " ++ s
            ++ frameString locals (eq_false_of_ne_true h)

def throwErrWithTrace (s : String) (k : Kont) : EvaluatorCEK α := do
  let {locals, ..} <- read
  let trace <- if k matches .halt then pure "" else k.trace
  let framestr := if h : locals.isEmpty then "" else frameString locals (eq_false_of_ne_true h)
  throwErr (s ++ framestr ++ trace)
--  if h : TreeMap.isEmpty locals
--  then throw $ TypingError.Lowlevel
--             $ "Interpreter: " ++ s
--            ++ "\nBacktrace:" ++ trace
--  else throw $ TypingError.Lowlevel
--             $ "Interpreter: " ++ s
--            ++ frameString locals (eq_false_of_ne_true h)
--            ++ "\nBacktrace:" ++ trace

/-- any error tagged Lowlevel should be (but isn't) caught by a previous pass
   e.g. typechecker
-/
scoped macro (name := «term_impossible!_») "impossible!" v:interpolatedStr(term) : term => ``(throwErr s!$v)
@[inherit_doc «term_impossible!_»]
scoped macro "impossibleF!" v:interpolatedStr(term) : term =>
  ``(throwErrWithFrame s!$v)
@[inherit_doc «term_impossible!_»]
scoped macro "impossibleT!" v:interpolatedStr(term) k:ident : term =>
  ``(throwErrWithTrace s!$v $k)

/--
applyHBinOp! op args key1 key2 node = node $ (args₁ : key1) `op` (args₂ : key2)
-/
scoped macro "applyHBinOp!" t:ident as:ident key1:ident key2:ident node:ident : term =>
  ``($key1 $as[0] >>= fun i =>
      $key2 $as[1] >>= fun j =>
        pure ($node ($t i j)))
/--
applyBinOp! op args key noed = node $ (args₁ : key) `op` (args₂ : key)
-/
scoped macro "applyBinOp!" t:ident as:ident key:ident node:ident : term =>
  ``(applyHBinOp! $t $as $key $key $node)

instance : Coe Int Value    := ⟨.int⟩
instance : Coe Bool Value   := ⟨.bool⟩
instance : Coe String Value := ⟨.str⟩
instance : Coe Unit Value   := ⟨fun _ => .unit⟩
scoped instance : MonadLift IO EvaluatorCEK
  := ⟨liftM ∘ EIO.adapt TypingError.Lowlevel ∘ liftEIO⟩

@[inline]
def expectInt : Value -> EvaluatorCEK Int
  | .int i => return i
  | v => impossibleF! "expected Int, found {v}"
def expectBool : Value -> EvaluatorCEK Bool
  | .bool b => return b
  | v => impossibleF! "expected Bool, found {v}"
def expectStr : Value -> EvaluatorCEK String
  | .str s => return s
  | v => impossibleF! "expected String, found {v}"

section Helpers
def asConst : TConst -> Value
  | .PUnit   => .unit
  | .PInt i  => .int i
  | .PStr s  => .str s
  | .PBool b => .bool b

def lookup (x : FVarId) : EvaluatorCEK Value := do
  let {topvals, locals,..} <- read
  match locals[x]? <|> topvals[x]? with
  | some v => return v
  | none   => do
    impossibleF! "unbound fvar #{x}: not cached in `topvals`. likely implementation error in `check`/`evaluate1`."

def evalAtom : Atom -> EvaluatorCEK Value
  | .lit k  => return asConst k
  | .erased => impossibleF! "unreachable code is reached"
  | .fvar x => lookup x

def projPair (s : FVarId) : Nat -> Value -> EvaluatorCEK Value
  | 0, .pair p _ => return p
  | 1, .pair _ q => return q
  | i, v => impossibleF! "invalid pair projection #{i} for #{s} => {v}"

def projConstr (s : FVarId) : Nat -> Value -> EvaluatorCEK Value
  | i, v@(.constr t as) =>
    if h : i < as.size then return as[i]
    else impossibleF! "invalid variant projection #{i} for #{s} => {v}"
  | i, v => impossibleF! "invalid variant projection #{i} for #{s} => {v}"

def evalPrimBinop (op : PrimOp) (args : Array Value) : EvaluatorCEK Value :=
  match op, h : args.size with
  | .add   , _ + 2 => applyBinOp! Add.add args expectInt  Value.int
  | .sub   , _ + 2 => applyBinOp! Sub.sub args expectInt  Value.int
  | .mul   , _ + 2 => applyBinOp! Mul.mul args expectInt  Value.int
  | .div   , _ + 2 => applyBinOp! Div.div args expectInt  Value.int
  | .eqInt , _ + 2 => applyBinOp! BEq.beq args expectInt  Value.bool
  | .eqBool, _ + 2 => applyBinOp! BEq.beq args expectBool Value.bool
  | .eqStr , _ + 2 => applyBinOp! BEq.beq args expectStr  Value.bool
  | op, _          => impossibleF! "cannot apply {repr op} to {args}"

def evalExtern (f : String) (args : Array Value) : EvaluatorCEK Value := do
  match externTab.findD f 0, h : args.size with
  | 0, n     => impossibleF! "undefined foreign function {f}/{n}"
  | 1, _ + 1 => println! format args[0]; return .unit
  | 2, _ + 1 => return format args[0] |>.pretty |> .str
  | 3, _ + 2 => applyBinOp! String.append args expectStr Value.str
  | 4, _ + 1 => IO.print "read> " *> IO.getStdin >>= liftM ∘ IO.FS.Stream.getLine >>= readValue
  | _, n     => impossibleF! "no implementation available for foreign function {f}/{n}"

open Format (fill group pretty nestD) in
def template {α} [ToFormat α] (name : String) (v : α) (ty : Scheme) : String :=
  let s := s!"{name} ="
  let ss := s.length
  if ss <= 20
  then pretty (fill $ (group $ s <> nestD (format v)) <+> "⊢" <> format ty)
              (width := 70) (indent := ss - 1) (column := ss - 1)
  else pretty (fill $ (group $ s ++ "\n" ++ format v) <+> "⊢" <> format ty)
              (width := 70) (indent := 2) (column := 2)
