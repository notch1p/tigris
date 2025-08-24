import Tigris.lexing
import PP.dependentPP

open Expr Lexing Parser Parser.Char

def List.rmDup [BEq α] [Hashable α] (l : List α) : List α :=
  let s : Std.HashSet α := ∅
  let rec go s
    | [] => []
    | x :: xs => if x ∈ s then go s xs else x :: go (insert x s) xs
  go s l

def List.mapReduce! [Inhabited β] (mapf : α -> β) (f : β -> β -> β) (xs : List α) : β :=
  match xs with
  | [] => panic! "empty list"
  | x :: xs => xs.foldl (flip $ flip f ∘ mapf) (mapf x)

def List.foldr1 (f : α -> α -> α) (xs : List α) (h : xs ≠ []) : α :=
  match xs with
  | [x] => x
  | x :: y :: xs => f x (foldr1 f (y :: xs) $ List.cons_ne_nil y xs)

def List.foldl2 (f : γ -> α -> β -> γ) (init : γ) : List α -> List β -> γ
  | x :: xs, y :: ys => foldl2 f (f init x y) xs ys
  | _, _ => init

def List.foldr2 (f : γ -> α -> β -> γ) (init : γ) : List α -> List β -> γ
  | x :: xs, y :: ys => f (foldr2 f init xs ys) x y
  | _, _ => init
section
variable {ε σ τ m α}
         [Parser.Stream σ τ]
         [Parser.Error ε σ τ]
         [Monad m]
/--
  `chainl1 p op` parses *one* or more occurrences of `p`, separated by `op`. Returns
  a value obtained by a **left** associative application of all functions returned by `op` to the
  values returned by `p`.
  - if there is exactly one occurrence of `p`, `p` itself is returned touched.
-/
partial def chainl1
  (p : ParserT ε σ τ m α)
  (op : ParserT ε σ τ m (α -> α -> α)) : ParserT ε σ τ m α := do
  let x <- p; rest x where
  rest x :=
    (do let f <- op; let y <- p; rest (f x y)) <|> pure x

partial def chainr1
  (p : ParserT ε σ τ m α)
  (op : ParserT ε σ τ m (α -> α -> α)) : ParserT ε σ τ m α := do
  let x <- p; rest x where
  rest x :=
    (do let f <- op; chainr1 p op <&> f x) <|> pure x

def warn (s : String) : TParser σ Unit :=
  modify fun (pe, a) =>
    (pe, a ++ Logging.warn s)
def error (s : String) : TParser σ Unit :=
  modify fun (pe, a) =>
    (pe, a ++ Logging.error s)


@[inline] def η₂ s :=
  fun e₁ e₂ => App (App s e₁) e₂

@[inline] def η₂'
  | App s _ => η₂' s
  | Fun _ e => η₂' e
  | e => e

@[inline] def infixOp (op : Symbol) (e : α -> α -> α) : TParser σ $ α -> α -> α :=
  (kw op) *> pure e

@[inline] def link s := η₂ $ Var s

namespace Parser.Error
def Simple.flatten
  [Parser.Stream σ τ]
  : Simple σ τ -> Stream.Position σ × Option τ × Array (Stream.Position σ × String)
  | .unexpected pos tok? => (pos, tok?, #[])
  | .addMessage e pos msg =>
    let (p, t, ms) := Simple.flatten e
    (p, t, ms.push (pos, msg))

def Simple.rebuild
  [Parser.Stream σ τ]
  (failPos : Stream.Position σ) (found? : Option τ) (msgs : Array (Stream.Position σ × String)) : Simple σ τ :=
  let base := Simple.unexpected failPos found?
  msgs.foldl (init := base) (fun acc (pos, m) => Simple.addMessage acc pos m)
end Parser.Error
section open Error
private def dedupMsgsAt
  (pos : Stream.Position Substring)
  (msgs : Array (Stream.Position Substring × String))
  : Array (Stream.Position Substring × String) :=
  let seen : Std.HashSet String := ∅
  (·.1) <| msgs.foldl (init := (#[], seen)) fun (out, seen) (p, m) =>
    if p == pos then
      if let (true, seen) := seen.containsThenInsert m then
        (out.push (p, m), seen)
      else (out, seen)
    else (out, seen)
def simpErrorCombine (e₁ : Simple Substring Char) (e₂ : Simple Substring Char) : Simple Substring Char :=
  let (p₁, f₁, m₁) := e₁.flatten
  let (p₂, f₂, m₂) := e₂.flatten
  if p₁ < p₂ then e₂ else if p₂ < p₁ then e₁ else
    let found := f₁ <|> f₂
    let merged := dedupMsgsAt p₁ (m₁ ++ m₂)
    Simple.rebuild p₁ found merged
end
def first'
  (ps : Array $ ParserT ε σ τ m α)
  (combine : ε → ε → ε)
  : ParserT ε σ τ m α := do
  let rec go n (h : n <= ps.size) e s :=
    match _ : n with
    | 0 => return .error s e
    | m + 1 =>
      let pss := ps.size
      have : m < pss := Nat.le_trans (Nat.lt.base _) h
      let savePos := Stream.getPosition s
      ps[pss - m.succ] s >>= fun
      | .ok s v => return .ok s v
      | .error s f =>
        go m (Nat.le_of_lt this) (combine e f) (Stream.setPosition s savePos)
  go ps.size (Nat.le.refl) (Error.unexpected (<- getPosition) none)

def treeParse
  (p : α -> ParserT ε σ τ m α)
  (root : Std.DTreeMap.Internal.Impl α (λ _ => β))
  (combine : ε -> ε -> ε := fun _ => id)
  : ParserT ε σ τ m (α × β) := getPosition >>= (go root $ Error.unexpected · none) where
  go rt (e : ε) s := do
    match rt with
    | .leaf => return .error s e
    | .inner _ k v l r =>
      match <- go l e s with
      | .ok s res => return .ok s res
      | .error s f =>
        let savePos := Stream.getPosition s
        match <- p k s with
        | .ok s res => return .ok s (res, v)
        | .error s f' =>
          go r (combine f f') (Stream.setPosition s savePos)


end

def Array.mapReduce! [Inhabited β] (mapf : α -> β) (f : β -> β -> β) (xs : Array α) : β :=
  if h : xs.size > 0 then
    xs[1:].foldl (flip $ flip f ∘ mapf) (mapf xs[0])
  else panic! "empty array"

def Array.mapReduce (mapf : α -> β) (f : β -> β -> β) (xs : Array α) (h : xs.size > 0) : β :=
  xs[1:].foldl (flip $ flip f ∘ mapf) (mapf xs[0])

def Array.foldl1 [Inhabited α] (f : α -> α -> α) (arr : Array α) : α :=
  let mf mx y := some $ match mx with | none => y | some x => f x y
  arr.foldl mf none |>.get!

def Array.foldr1 [Inhabited α] (f : α -> α -> α) (arr : Array α) : α :=
  let mf x my := some $ match my with | none => x | some y => f x y
  arr.foldr mf none |>.get!

def isNotOpInit
  | '_' | ',' | '(' | ')' | ' '
  | '{' | '}' | '[' | ']' => false
  | c => not $ c.isDigit || c >= '\t' && c <= '\r'

def isNotOpCand
  | '_' | ',' | '(' | ')' | ' '
  | '{' | '}' | '[' | ']' => false
  | c => not $ c >= '\t' && c <= '\r'

def potentialOp : TParser σ String := do
  let hd <- tokenFilter isNotOpInit
  let tl <- takeMany $ tokenFilter isNotOpCand
  return tl.foldl String.push hd.toString
local infixl:40 " <? " => flip (· <|> ·)

def takeBindingOp? (minPrec : Nat) : TParser σ (Option (String × OpEntry)) :=
  pure none <? do
  let tokSpan <- spaces *> lookAhead potentialOp
  let ({ops,..}, _) <- get
  match ops.matchPrefix tokSpan 0 with
  | none => throwUnexpected
  | some entry@{sym,prec,..} =>
    if prec < minPrec then
      throwUnexpectedWithMessage none "prec too low"
    if let some revop := reservedOp.matchPrefix tokSpan 0
    then
      if sym.length > revop.length then
        string sym *> return some (sym, entry)
      else
        throwUnexpectedWithMessage none "reserved"
    else
      string sym *> return some (sym, entry)

def hole i := s!"__?x{Nat.toSubscriptString i}"

--instance prodSizeOf [SizeOf α] [SizeOf β] : SizeOf $ α × β where
--  sizeOf p := sizeOf p.fst + sizeOf p.snd + 1
--
--theorem prod_fst_lt_self [SizeOf α] [SizeOf β] (p : α × β) : sizeOf p.1 < sizeOf p := by
--  simp+arith[sizeOf]
--
--theorem prod_snd_lt_self [SizeOf α] [SizeOf β] (p : α × β) : sizeOf p.2 < sizeOf p := by
--  simp+arith[sizeOf]

infixr:80 " <> " => Nat.lt_trans
open ST in
def transformPrim (e : Expr) : ST σ (Expr × Nat) := do
  let cnt : Ref σ Nat <- mkRef 0
  let rec go : Expr -> ST σ Expr
    | Var "_" | Var "·" =>
      cnt.modifyGet fun cnt => ((Var $ hole cnt), cnt + 1)
    | App f a =>
      App <$> go f <*> go a
    | Prod' l r => Prod' <$> go l <*> go r
    | Fun x e => Fun x <$> go e
    | Fix e => Fix <$> go e
    | Fixcomb e => Fixcomb <$> go e
    | Cond c t e => Cond <$> go c <*> go t <*> go e
    | Match e discr =>
      Match <$> e.mapM go <*> discr.attach.mapM fun ⟨pe, property'⟩ =>
        have : sizeOf pe.2 < 1 + sizeOf e + sizeOf discr := by
          have h₁ := (prod_sizeOf_lt pe).2 <> Array.sizeOf_lt_of_mem property'
          omega
        (pe.1, ·) <$> go pe.2
    | e => return e

  (· , ·) <$> (go e) <*> cnt.get

@[inline] def transShorthand (e : Expr) : Expr :=
  let (e, n) := runST fun _ => transformPrim e
  n.foldRev (fun i _ a => Fun (hole i) a) e

@[inline] def templateREPL id v t := id ++ " = " ++ v ++ " ⊢ " ++ t

@[inline] def liftEIO (act : IO α) : EIO String α := IO.toEIO IO.Error.toString act
