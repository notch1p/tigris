import Tigris.typing.ttypes
import Tigris.parsing.types
import Tigris.lexing

structure ParamInfo where
  ordered : Array (String × Kind)
  /-- Local binder kinds (mirrors `ordered`). -/
  kinds : Std.HashMap String Kind
deriving Repr
@[inline] def ParamInfo.empty : ParamInfo := ⟨#[], {}⟩

def ParamInfo.merge : ParamInfo -> ParamInfo -> ParamInfo
  | ⟨ordered₁, kinds₁⟩, ⟨ordered₂, kinds₂⟩ =>
    { ordered := ordered₂.foldl (init := ordered₁) fun a ord =>
        if let some idx := ordered₁.findIdx? $ (·.1 == ord.1) then
          a.set! idx ord
        else a.push ord
    , kinds := kinds₁ ∪ kinds₂}
instance : Union ParamInfo := ⟨.merge⟩
instance : EmptyCollection ParamInfo := ⟨.empty⟩

namespace Parsing
namespace PType open Parsing Lexing MLType Parser Parser.Char Lexing
variable {σ}

def getTyArity (name : String) : TParser σ $ Option (Kind × Bool) := do
  get <&> (·.1.tys.find? name)

mutual
/-- Atomic kind: `Type` or a parenthesized kind. -/
partial def kindAtom : TParser σ Kind :=
  (kw "Type" $> Kind.type) <|> parenthesized kindArrow

/-- Right-associative arrow chain of kinds: `Type`, `Type -> Type`,
`(Type -> Type) -> Type`, … -/
partial def kindArrow : TParser σ Kind := do
  let lhs <- kindAtom
  (ARROW *> kindArrow >>= fun rhs => pure (.karr lhs rhs)) <|> pure lhs
end

/-- Parse a kind expression. -/
@[inline] def parseKind : TParser σ Kind := kindArrow

def parseKV : TParser σ (String × Kind) := ID <&> fun id => (id, .type)

def parseParam : TParser σ (String × Kind) := parseKV <? parenthesized do
  let id <- ID
  if <- test COLON then
    spaces
    let k <- parseKind
    pure (id, k)
  else pure (id, .type)

def parseParams : TParser σ ParamInfo := do
  let ps <- takeMany parseParam
  if ps.hasDuplicates Prod.fst then
    error "duplicate type parameter name\n"
    throwUnexpected
  if ps.any (String.isUpperInit ∘ Prod.fst) then
    error "bound type constructors/variables must begin with lowercase letter\n"
    throwUnexpected
  let kinds := ps.foldl (fun m (n, k) => m.insert n k) {}
  return {ordered := ps, kinds}

def getLocalTyArity (pinfo : ParamInfo) (name : String)
  : TParser σ (Option (Kind × Bool)) := do
  match pinfo.kinds[name]? with
  | some k =>
    if k.arity = 0 then pure none
    else
      pure (some (k, false))
  | none => getTyArity name

def registerTy (name : String) (kind : Kind) (mt : Bool) (flag := true) : TParser σ Unit := do
  if let true <- modifyGet fun orig@(st@{tys,..}, l) =>
    match tys.find? name with
    | none =>
      (true, {st with tys := tys.insert name (kind, flag)}, l)
    | some (kind', k) =>
      -- Reconcile via kind unification — exact equality is too strict if
      -- the registered/expected kinds mention `kvar`s during inference.
      match Kind.unify kind' kind with
      | .ok _ =>
        if mt then
          if !k && flag then (true, {st with tys := tys.insert name (kind, flag)}, l)
          else (true, orig)
        else
          let err := Logging.error
            "types are dynamically scoped: for this reason they may not be redefined.\n"
          (false, st, l ++ err)
      | .error _ =>
        let err := Logging.error $
          if mt then
            s!"mutual inductive type {Logging.magenta name} kind mismatch,\n\
              expected {kind'} but received {kind}\n"
          else s!"type {Logging.magenta name} kind mismatch: {kind'} vs {kind}\n"
        (false, st, l ++ err)
  then return ()
  else throwUnexpected

@[inline] def registerTyArity (name : String) (arity : Nat) (mt : Bool) (flag := true) : TParser σ Unit :=
  let rec mk : Nat -> Kind
    | 0     => .type
    | n + 1 => .karr .type (mk n)
  registerTy name (mk arity) mt flag

@[inline] def kindOfParams (ps : Array (String × Kind)) : Kind :=
  ps.foldr (fun (_, k) acc => .karr k acc) .type

mutual
/--
- `TCon` for upper-case tyctors,
- `TVar` for local lowercase tvs
- placeholder `TCon` for forward-referencing in mutual block. -/
partial def tyCtor (param : ParamInfo) : TParser σ MLType := do
  let id <- ID
  if id.isUpperInit then return TCon id
  else
    match param.kinds[id]? with
    | some _ => return TVar (.mkTV id)
    | none =>
      error s!"unbound type variable {id}\n"
      throwUnexpected

partial def tyApps (mt : Bool) (param : ParamInfo) : TParser σ MLType := withErrorMessage "TyTerm" do
  let hd <- tyAtom mt param
  match hd with
  | .TCon h =>
    match <- getTyArity h with
    | some (k, _) =>
      let args <- takeUpTo k.arity $ tyAtom mt param
      return MLType.mkApp (.TCon h) args.toList
    | none =>
      if mt then -- Forward reference
        modify fun (pe@{undTy,..}, s) => ({pe with undTy := h :: undTy}, s)
        let args <- takeMany $ tyAtom mt param
        registerTyArity h args.size mt false
        return MLType.mkApp (.TCon h) args.toList
      else
        error s!"undefined type {Logging.magenta h}\n"
        throwUnexpected
  | .TVar v =>
    let k := param.kinds.getD v.toStr .type
    let args <- takeUpTo k.arity $ tyAtom mt param
    return MLType.mkApp (.TVar v) args.toList
  | _ => return hd

partial def tyProd (mt : Bool) (param : ParamInfo) : TParser σ MLType := do
  let t₁ <- tyApps mt param
  let tn <- takeMany (ws (char '×' <|> char '*') *> tyApps mt param)
  return (t₁ :: tn.toList).foldr1 TProd (List.cons_ne_nil _ _)

partial def tyArrow (mt : Bool) (param : ParamInfo) : TParser σ MLType := do
  let lhs <- tyProd mt param
  (ARROW *> tyArrow mt param >>= fun rhs => pure $ TArr lhs rhs) <|> pure lhs

partial def tyAtom (mt : Bool) (param : ParamInfo) : TParser σ MLType :=
  tyCtor param <|> parenthesized (tyArrow mt param)
end

def tyEmpty : TParser σ TyDecl := do
  TYPE let tycon <- ID let {ordered,..} <- parseParams;
  return {tycon, param := ordered, ctors := #[]}

@[inline, always_inline]
def tyExp (paramInfo : ParamInfo := ∅) : TParser σ MLType := tyArrow false paramInfo

def tyPred (param : ParamInfo) : TParser σ Pred := do
  let ty <- tyArrow false param
  match ty with
  | .TApp (.TCon s) l => return ⟨s, l⟩
  | .TCon s           => return ⟨s, []⟩
  | _ => error s!"not a valid predicate" *> throwUnexpected
@[inline] def tyPreds (param : ParamInfo) : TParser σ (Array Pred) := sbrack $ sepBy1 COMMA $ tyPred param

def tyForall (mt : Bool) (param : ParamInfo) : TParser σ MLType := withErrorMessage "TyForall" do
  let param'@{ordered,..} <- optionD ((FORALL <|> FORALL') *> parseParams) ∅
  let param := param ∪ param'
  let pred <- optionD (tyPreds param) #[] <&> Array.toList
  if ordered.isEmpty && pred.isEmpty then tyArrow mt param
  else
    COMMA
    .TSch <$> .Forall (ordered.foldr (.cons ∘ .mkTV ∘ Prod.fst) []) pred <$> tyArrow mt param

def tyField (mt : Bool) (param : ParamInfo) : TParser σ (Symbol × MLType) := withErrorMessage "TyField" do
  let id <- ID; COLON; let ty <- tyForall mt param
  return (id, ty)

def tyScheme : TParser σ Scheme := do
  let param@{ordered,..} <- optionD ((FORALL <|> FORALL') *> parseParams) ∅
  let pred <- optionD (tyPreds param) #[] <&> Array.toList
  if !ordered.isEmpty || !pred.isEmpty then COMMA
  .Forall (ordered.foldr (.cons ∘ .mkTV ∘ Prod.fst) []) pred <$> tyExp param

def tyInstScheme : TParser σ (Scheme × ParamInfo) := do
  let param@{ordered,..} <- optionD ((FORALL <|> FORALL') *> parseParams) ∅
  let pred <- optionD (tyPreds param) #[] <&> Array.toList
  if !ordered.isEmpty || !pred.isEmpty then COMMA
  (·, param) <$> .Forall (ordered.foldr (.cons ∘ .mkTV ∘ Prod.fst) []) pred <$> tyExp param

def tyRecord (tycon : String) (param : ParamInfo) (mt : Bool) (offside? : Bool)
  : TParser σ TyDecl := withErrorMessage "TyRecord" do
  let fields <-
    if offside? then alignedBindings (tyField mt param)
    else sepBy COMMA (tyField mt param)
  let (fids, tys) := fields.unzip
  if fids.hasDuplicates id then
    error "duplicated fields not allowed in structure definition\n"
    throwUnexpected

  registerTy tycon (kindOfParams param.ordered) mt

  modify fun (st@{recordFields,..}, l) =>
    ({st with recordFields := recordFields.insert tycon fids}, l)
  return  { tycon
          , param := param.ordered
          , ctors := #[(tycon, fields.toList, tys.size)]}

def tyDecl (mt : Bool) : TParser σ TyDecl := withErrorMessage "TyDecl" do
  let cls? <- TYPE?
  let tycon <- ID
  if tycon.isUpperInit then
    let param <- parseParams;
    first $
      [ EQ *> do
          if <- test (kwOpExact "{") then
            let tydecl <- tyRecord tycon param mt false <* kwOpExact "}"
            return {tydecl with cls?}
          else
            registerTy tycon (kindOfParams param.ordered) mt
            let hd <- (optional BAR *> ctor mt param)
            let tl <- takeMany (BAR *> ctor mt param)
            return {tycon, param := param.ordered, ctors := #[hd] ++ tl, cls?}
      , WHERE *> tyRecord tycon param mt true <&> fun tydecl => {tydecl with cls?}]

  else
    error "type constructor must begin with an uppercase letter\n"
    throwUnexpected
where
  ctor mt param := do
    let cname <- ID
    if cname.isUpperInit then
      let args <- takeMany (parenthesized (tyForall mt param) <|> (tyForall mt param))
      let namedArgs := Prod.fst $ args.foldr (init := ([], 0)) fun s (a, i) =>
        ((s!"cname_{i}", s) :: a, i + 1)
      return (cname, namedArgs, args.size)
    else
      error "value constructor must begin with an uppercase letter\n"
      throwUnexpected

end PType

end Parsing
