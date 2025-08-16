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

def List.foldl2 (f : γ -> α -> β -> γ) (init : γ) : List α -> List β -> γ
  | x :: xs, y :: ys => foldl2 f (f init x y) xs ys
  | _, _ => init

def List.foldr2 (f : γ -> α -> β -> γ) (init : γ) : List α -> List β -> γ
  | x :: xs, y :: ys => f (foldr2 f init xs ys) x y
  | _, _ => init
namespace Logging open PrettyPrint Text
def blue s := (show SString from ⟨s, [], .blue, .defaultColor⟩).render
def cyan s := (show SString from ⟨s, [], .green, .defaultColor⟩).render
def magenta s := (show SString from ⟨s, [], .magenta, .defaultColor⟩).render
def note s := (show SString from ⟨"[NOTE] ", [.bold], .cyan, .defaultColor⟩).render ++ s
def info s := (show SString from ⟨"[INFO] ", [.bold], .blue, .defaultColor⟩).render ++ s
def warn s := (show SString from ⟨"[WARN] ", [.bold], .yellow, .defaultColor⟩).render ++ s
def error s := (show SString from ⟨"[ERROR] ", [.bold], .red, .defaultColor⟩).render ++ s
end Logging
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

@[inline] def η₂ s :=
  fun e₁ e₂ => App (App s e₁) e₂

@[inline] def η₂'
  | App s _ => η₂' s
  | Fun _ e => η₂' e
  | e => e

@[inline] def infixOp (op : Symbol) (e : α -> α -> α) : TParser σ $ α -> α -> α :=
  (kw op) *> pure e

@[inline] def link s := η₂ $ Var s

def first'
  (ps : Array $ ParserT ε σ τ m α)
  (combine : ε → ε → ε := fun _ => id)
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

def potentialOp : TParser σ String := ws do
  let hd <- tokenFilter $ not ∘ fun c => c == '_' || c.isDigit || c == ',' || c == ')' || c == ' ' || c >= '\t' && c <= '\r'
  let tl <- takeMany $ tokenFilter $ not ∘ fun c => c == ',' || c == ')' || c == ' ' || c >= '\t' && c <= '\r'
  return tl.foldl String.push hd.toString

def takeBindingOp? (minPrec : Nat) : TParser σ (Option (String × OpEntry)) :=
  (withBacktracking $ show TParser σ (Option $ String × OpEntry) from do
     let tok <- potentialOp
     let ({ops,..}, _) <- get
     match ops.get? tok with
     | none => throwUnexpectedWithMessage none "not an operator"
     | some entry@{prec,..} =>
       if prec < minPrec then
         throwUnexpectedWithMessage none "prec too low"
       else return some (tok, entry))
  <|> pure none

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

def transShorthand (e : Expr) : Expr :=
  let (e, n) := runST fun _ => transformPrim e
  n.foldRev (fun i _ a => Fun (hole i) a) e

def templateREPL id v t := id ++ " = " ++ v ++ " ⊢ " ++ t

def liftEIO (act : IO α) : EIO String α := IO.toEIO IO.Error.toString act
