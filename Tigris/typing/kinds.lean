import Tigris.typing.ttypes

structure KindEnv where
  /-- declared tyctor's kind view -/
  tycon : String -> Option Kind
  /--
    TVs get kind metavariables lazily, memoized unconditionally, thanks
    to the new, proper encoding of TV
  -/
  tv    : Std.TreeMap TV Kind := ∅
  ks    : KSubst := ∅
  nxt   : Nat := 0
deriving Inhabited

instance : EmptyCollection KindEnv := ⟨{tycon := fun _ => none}⟩

namespace KindEnv

def ofEnv : Env -> KindEnv
  | {tyDecl, clsInfo,..} =>
    {tycon := fun name =>
        match tyDecl[name]? with
        | some td => some $ kindOfParams td.param
        | none =>
          match clsInfo[name]? with
          | some ci => some $ kindOfParams ci.params
          | none =>
            match name with
            | "Int" | "Bool" | "String" | "Unit" | "Empty" => some .type
            | _ => none}

/-- a kind variable is denoted ?k.N -/
@[inline] def freshKV (ke : KindEnv) : KindEnv × Kind :=
  let n := ke.nxt
  ({ke with nxt := n + 1}, .kvar n)

def kindUnify (ke : KindEnv) (k₁ k₂ : Kind) : Except MLType.TypingError KindEnv :=
  let k₁ := Kind.apply ke.ks k₁
  let k₂ := Kind.apply ke.ks k₂
  match Kind.unify k₁ k₂ with
  | .ok s    => pure {ke with ks := s ∪ₖ ke.ks}
  | .error _ => throw $ .KindMismatch k₁ k₂

/-- a fresh kvar. Outside of this module, this should be used, instead of freshKV
    as it memoizes metavariables. -/
def bindBinder (ke : KindEnv) (v : TV) : KindEnv × Kind :=
  let (ke, k) := freshKV ke
  ({ke with tv := ke.tv.insert v k}, k)

end KindEnv

def Kind.defaultKV : Kind -> Kind
  | .kvar _ => .type
  | .karr a b => .karr (defaultKV a) (defaultKV b)
  | t => t

/-- recover the kind of a type. Notably:
- TApp constrains the head kind to a fresh arrow and checks the argument against its domain;
- TArr/TProd components must be Type:
- TyLam/TSch binders are fresh kind metavariables whose constraints
  accumulate in ks.
-/
partial def ConstraintInfer.kindOf (ke : KindEnv) : MLType -> Except MLType.TypingError (KindEnv × Kind)
  | .TVar v =>
    match ke.tv[v]? with
    | some k => return (ke, k)
    | none =>
      let (ke, k) := KindEnv.freshKV ke
      return ({ke with tv := ke.tv.insert v k}, k)
  | .TCon h =>
    match ke.tycon h with
    | some k => return (ke, k)
    | none =>
      let (ke, k) := KindEnv.freshKV ke
      return (ke, k)
  | t₁ ->' t₂ | t₁ ×'' t₂ => do
    let (ke, k₁) <- kindOf ke t₁
    let (ke, k₂) <- kindOf ke t₂
    let ke <- KindEnv.kindUnify ke k₁ .type
    let ke <- KindEnv.kindUnify ke k₂ .type
    return (ke, .type)
  | .TApp h args => do
    let (ke, kh) <- kindOf ke h
    args.foldlM (init := (ke, kh)) fun (ke, k) a => do
      let (ke, ka) <- kindOf ke a
      -- pretty much the same as a basic HM term-level application.
      let (ke, d) := KindEnv.freshKV ke
      let (ke, r) := KindEnv.freshKV ke
      let ke <- KindEnv.kindUnify ke k (.karr d r)
      let ke <- KindEnv.kindUnify ke d ka
      return (ke, r)
  | .TyLam x body => do
    let (ke, kx) := KindEnv.bindBinder ke x
    let (ke, k) <- kindOf ke body
    return (ke, .karr (Kind.apply ke.ks kx) $ Kind.apply ke.ks k)
  | .TSch (.Forall vs _ps t) => do
    let ke := vs.foldl (fun ke v => (KindEnv.bindBinder ke v).1) ke
    let (ke, k) <- kindOf ke t
    return (ke, Kind.apply ke.ks k)
