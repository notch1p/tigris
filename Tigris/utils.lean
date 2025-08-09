import Tigris.lexing

open Expr Lexing Parser Parser.Char

def List.rmDup [BEq α] [Hashable α] (l : List α) : List α :=
  let s : Std.HashSet α := ∅
  let rec go s
    | [] => []
    | x :: xs => if x ∈ s then go s xs else x :: go (insert x s) xs
  go s l

def List.mapReduce! [Inhabited β] (mapf : α -> β) (f : β -> β -> β) (xs : List α) : β :=
  match xs with
  | [] => default
  | x :: xs => xs.foldl (flip $ flip f ∘ mapf) (mapf x)

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
  | App (App s _) _ => s
  | s => s

@[inline] def infixOp (op : Symbol) (e : α -> α -> α) : TParser $ α -> α -> α :=
  (kw op) *> pure e

@[inline] def link s := η₂ $ Var s

@[inline] def buildOpParser
  (p : TParser α)
  (table : OpTable α)
  : TParser α := table.foldl (init := p) fun a (_, s) (e, assoc) =>
    match assoc with
    | .leftAssoc => chainl1 a $ infixOp s e
    | .rightAssoc => chainr1 a $ infixOp s e

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

def Array.foldl1 [Inhabited α] (f : α -> α -> α) (arr : Array α) : α :=
  let mf mx y := some $ match mx with | none => y | some x => f x y
  arr.foldl mf none |>.get!

def Array.foldr1 [Inhabited α] (f : α -> α -> α) (arr : Array α) : α :=
  let mf x my := some $ match my with | none => x | some y => f x y
  arr.foldr mf none |>.get!
