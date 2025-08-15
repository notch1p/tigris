import Tigris.typing.types
import Tigris.parsing.types
import Tigris.parsing.ptype
import Tigris.interpreter.types
import Tigris.interpreter.entrypoint

namespace Interpreter open Parsing PType Value MLType TV Pattern Expr TypingError
def registerData (E : Env) (VE : VEnv) : TyDecl -> IO (Env × VEnv)
  | ty@{ctors,tycon,param} =>
    ctors.foldlM (init := (E, VE)) fun (E, {env := VE}) (cname, fields) =>
      let s := ctorScheme tycon (param |>.map mkTV |>.toList) fields
      let arity := fields.length
      let v := if arity == 0 then .VConstr cname #[]
                             else .VCtor cname arity #[]
      (⟨E.1.insert cname s, E.2.insert tycon ty⟩, ⟨VE.insert cname v⟩) <$ println! "{cname} = {v.render} ⊢ {s.render}"

def binop (n : Nat) (h : n ∈ [1,2,3,4]) : Int -> Int -> Int :=
  match n with
  | 1 => (· + ·) | 2 => (· - ·) | 3 => (· * ·) | 4 => (· / ·)

def evalPat1 (v : Value) (VE : VEnv) (acc : Array $ Symbol × Value) : Pattern -> Option (VEnv × Array (Symbol × Value))
  | PWild => some (VE, acc)
  | PConst c =>
    match c, v with
    | .PInt i , .VI i' => if i == i' then some (VE, acc) else none
    | .PStr s , .VS s' => if s == s' then some (VE, acc) else none
    | .PBool b, .VB b' => if b == b' then some (VE, acc) else none
    | .PUnit  , .VU    => some (VE, acc)
    | _, _ => none

  | PVar x => some (⟨VE.env.insert x v⟩, acc.push (x, v))

  | PProd' p₁ p₂ =>
    if let VP v₁ v₂ := v then
      if let some (⟨E₁⟩, acc) := evalPat1 v₁ VE acc p₁  then
        if let some (E₂, acc) := evalPat1 v₂ ⟨(VE.env ∪ E₁)⟩ acc p₂ then
          some (E₂, acc)
        else none
      else none
    else none

  | PCtor n as =>
    match v with
    | .VConstr c fs =>
      if h : c ≠ n ∨ fs.size ≠ as.size then none
      else
        let (ve, flag, acc) := as.size.fold (init := (VE.env, true, acc)) fun i _ (VE, _) =>
          have : fs.size = as.size := not_or.mp h |>.2 |> Classical.not_not.mp
          match evalPat1 fs[i] ⟨VE⟩ acc as[i] with
          | some (ve, acc) => (VE ∪ ve.env, true, acc)
          | none           => (VE, false, acc)
        if flag then some (⟨ve⟩, acc) else none
    | _ => none

def evalPat (E : VEnv) (ps : Array Pattern) (vals : Array Value) : Option VEnv := do
  if ps.size ≠ vals.size then none
  else
    let mut (E, flag) := (E, true)
    for p in ps, v in vals do
      if let some (e, _) := evalPat1 v E #[] p then
        E := e
        flag := true
      else flag := false break
    if flag then some E else none

def callForeign (as' : Value) (n : Nat) : Value :=
  let as := match as' with | VP v₁ v₂ => [v₁, v₂] | _ => [as']
  have : List.length as > 0 := by cases as' <;> simp[as]
  match h : n with
  | 1 | 2 | 3 | 4 =>
    if let t@(VI i, VI i') := (as[0], as[1]!) then
      VI $ (binop n $ by simp[h]) i i'
    else unreachable!
  | 5 =>
    if let (VB b) := as[0] then
      VB $ b.not
    else unreachable!
  | 6 =>
    let rec go : Value -> Value -> Except Value Bool
      | VI i, VI i' | VB i, VB i' | VS i, VS i' | VOpaque i, VOpaque i' =>
        pure $ i == i'
      | VU, VU => pure true
      | VF .., VF .. => throw $ VEvalError s!"equality handler is not implemented for function type"
      | VP l r, VP l' r' => (· && ·) <$> go l l' <*> go r r'
      | x, y => unreachable!
    match go as[0] as[1]! with
    | .ok x => VB x | .error e => e
  | 7 => if let (VI i) := as[0] then VI $ i + 1 else unreachable!

  | n => .VOpaque n

partial def eval (E : VEnv) : Expr -> Except TypingError Value
  | CI v => pure $ VI v | CS v => pure $ VS v | CB v => pure $ VB v | CUnit => pure VU
  | Var x => match E.env.get? x with | some x => pure x | none => throw $ Undefined x
  | Fun x body => pure $ VF x body E
  | Fix e | Fixcomb e =>
    eval E e >>= fun
    | VF fname fbody E' =>
      pure $ VFRec fname fbody E'
    | _ => unreachable!
  | App f a => do
    match <- eval E f with
    | VF s body E' =>
      let e <- eval E a
      let E' := E'.env.insert s e
      eval ⟨E'⟩ body
    | VOpaque n =>
      let a <- eval E a
      pure $ callForeign a n
    | self@(VFRec fname fbody E') =>
      let e <- eval E a
      let recE := E'.env.insert fname self
      match fbody with
      | Fun x body =>
        eval ⟨recE.insert x e⟩ body
      | _ => unreachable!
    | .VCtor name ar acc =>
      let v <- eval E a
      let acc' := acc.push v
      if acc'.size == ar then
        pure $ .VConstr name acc'
      else pure $ .VCtor name ar acc'
    | _ => unreachable!
  | Let x e body => do
    let e' <- eval E e
    let E' := E.env.insert x e'
    eval ⟨E'⟩ body
  | Cond c t e => do
    let e' <- eval E c
    match e' with
    | VB true => eval E t
    | VB false => eval E e
    | _       => throw $ WrongCardinal 2
  | Prod' e₁ e₂ => do
    pure $ VP (<-eval E e₁) (<-eval E e₂)
  | Match e discr => do
    let v <- e.mapM (eval E)
    let rec tryDiscriminant i (h : i <= discr.size) :=
      match i with
      | 0 => throw $ NoMatch e (toString $ v.map (·.render)) discr
      | j + 1 =>
        let (p, body) := discr[discr.size - j.succ]
        match evalPat E p v with
        | some bs =>
          eval bs body
        | none => tryDiscriminant j $ Nat.le_of_succ_le h
    tryDiscriminant discr.size Nat.le.refl

@[always_inline, inline] def parse! s := parse s |>.toOption |>.get!
@[always_inline, inline] def eval! s (e : VEnv := ⟨∅⟩) := parse! s |> eval e |>.toOption |>.get!

def arityGen (prim : Symbol) (arity : Nat) (primE : VEnv := ⟨∅⟩) : Value :=
  let rec go s
  | 0 => App (Var prim) s
  | 1 => Fun s!"__?g1" (App (Var prim) (Prod' s $ Var "__?g1"))
  | t@(n + 2) =>
    Fun s!"__?g{t}" $ (go (Prod' s (Var s!"__?g{t}")) (n + 1))
  Option.get!
  $ Except.toOption
  $ eval primE
  $ Fun s!"__?g{arity}"
  $ Fun s!"__?g{arity - 1}"
  $ go (Prod' (Var s!"__?g{arity}") (Var s!"__?g{arity - 1}")) (arity - 2)

@[inline, always_inline]
abbrev ag (prim : Symbol) (arity : {n // n > 1}) (primE : VEnv := ⟨∅⟩) : Value :=
  arityGen prim arity primE

def prim :=
  [ ("id"   , eval! "fun x => x")
  , ("rec"  , VOpaque 0)
  , ("__add", VOpaque 1)
  , ("__sub", VOpaque 2)
  , ("__mul", VOpaque 3)
  , ("__div", VOpaque 4)
  , ("not"  , VOpaque 5)
  , ("__eq" , VOpaque 6)
  , ("succ" , VOpaque 7)]
def prim' : VEnv := ⟨.ofList prim⟩

scoped macro n:term "of!" s:term : term => `(($n, (ag (String.append "__" $n) ⟨$s, by omega⟩ prim')))
abbrev defaultVE : VEnv where
  env := .ofList $ prim
  ++ [ "add" of! 2
     , "sub" of! 2
     , "mul" of! 2
     , "div" of! 2
     , "eq"  of! 2]

end Interpreter
