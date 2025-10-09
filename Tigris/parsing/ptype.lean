import Tigris.typing.ttypes
import Tigris.parsing.types
import Tigris.lexing

structure ParamInfo where
  ordered : Array (String × Nat)
  arity : Std.HashMap String Nat
@[inline] def ParamInfo.empty : ParamInfo := ⟨#[], {}⟩

def ParamInfo.merge : ParamInfo -> ParamInfo -> ParamInfo
  | ⟨ordered₁, arity₁⟩, ⟨ordered₂, arity₂⟩ =>
    { ordered := ordered₂.foldl (init := ordered₁) fun a ord =>
        if let some idx := ordered₁.findIdx? $ (·.1 == ord.1) then
          a.set! idx ord
        else a.push ord
    , arity := arity₁ ∪ arity₂}
instance : Union ParamInfo := ⟨.merge⟩
instance : EmptyCollection ParamInfo := ⟨.empty⟩

namespace Parsing
namespace PType open Parsing Lexing MLType Parser Parser.Char Lexing
variable {σ}

def getTyArity (name : String) : TParser σ $ Option (Nat × Bool) := do
  get <&> (·.1.tys.find? name)

def parseParam : TParser σ (String × Nat) := (parenthesized do
  let ascription := do
    let id <- ID
    if <- test COLON then
      let n <- spaces *> intLit
      pure (id, n.toNat)
    else pure (id, 0)
  ascription) <|> (ID <&> fun id => (id, 0))

def parseParams : TParser σ ParamInfo := do
  let ps <- takeMany parseParam
  if ps.hasDuplicates Prod.fst then
    error "duplicate type parameter name\n"
    throwUnexpected
  let arity := ps.foldl (fun m (n, a) => m.insert n a) {}
  return {ordered := ps, arity}

def getLocalTyArity (pinfo : ParamInfo) (name : String)
  : TParser σ (Option (Nat × Bool)) := do
  match pinfo.arity[name]? with
  | some k =>
    if k = 0 then pure none
    else
      pure (some (k, false))
  | none => getTyArity name

def registerTy (name : String) (arity : Nat) (mt : Bool) (flag := true) : TParser σ Unit := do
  if let true <- modifyGet fun orig@(st@{tys,..}, l) =>
    match tys.find? name with
    | none =>
      (true, {st with tys := tys.insert name (arity, flag)}, l)
    | some (arity', k) =>
      if arity' == arity && mt then
        if !k && flag then (true, {st with tys := tys.insert name (arity, flag)}, l)
        else (true, orig)
      else
        let err := Logging.error $
          if mt then
            s!"mutual inductive type {Logging.magenta name} arity mismatch,\n\
              expected {arity'} but received {arity}\n"
          else s!"types are dynamically scoped: for this reason they may not be redefined.\n"
        (false, st, l ++ err)
  then return ()
  else throwUnexpected

mutual
partial def tyCtor (param : ParamInfo) : TParser σ MLType := do
  let id <- ID
  if isUpperInit id then return TApp id []
  else
    match param.arity[id]? with
    | some 0 => return TVar (.mkTV id)
    | some _ =>
      return TApp id []
    | none =>
      error s!"unbound type variable {id}\n"
      throwUnexpected

partial def tyApps (mt : Bool) (param : ParamInfo) : TParser σ MLType := withErrorMessage "TyTerm" do
  let hd <- tyAtom mt param
  match hd with
  | .TApp h [] =>
    match <- getLocalTyArity param h with
    | some (0, _) => return TCon h
    | some (k, _) =>
      let args <- take k $ tyAtom mt param
      let extra <- takeMany $ tyAtom mt param
      if extra.isEmpty then
        if param.arity.getD h 0 > 0 then
          return KApp (.mkTV h) args.toList
        else return TApp h args.toList
      else
        error s!"type {Logging.magenta h} arity mismatch, \
              expected {k} but received {k + extra.size}\n"
        throwUnexpected
    | none =>
      match <- getTyArity h with
      | some (0, _) => return TCon h
      | some (k, _) =>
        let args <- take k $ tyAtom mt param
        let extra <- takeMany $ tyAtom mt param
        if extra.isEmpty then return TApp h args.toList
        else
          error s!"type {Logging.magenta h} arity mismatch, expected {k} but got {k + extra.size}\n"
          throwUnexpected
      | none =>
        if mt then
          modify fun (pe@{undTy,..}, s) => ({pe with undTy := h :: undTy}, s)
          let arg <- takeMany $ tyAtom mt param;
          registerTy h arg.size mt false
          return TApp h arg.toList
        else
          error s!"undefined type {Logging.magenta h}\n"
          throwUnexpected
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

def tyForall (mt : Bool) (param : ParamInfo) : TParser σ MLType := withErrorMessage "TyForall" $
  optionD ((FORALL <|> FORALL') *> parseParams) ∅ >>= fun param'@{ordered,..} =>
    -- we do not parse preds yet. not supported currently anyway.
    if ordered.isEmpty then tyArrow mt param
    else COMMA *>
      .TSch <$> (.Forall (ordered.foldr (.cons ∘ .mkTV ∘ Prod.fst) []) [] <$> tyArrow mt (param ∪ param'))

def tyField (mt : Bool) (param : ParamInfo) : TParser σ (Symbol × MLType) := withErrorMessage "TyField" do
  let id <- ID; COLON; let ty <- tyForall mt param
  return (id, ty)

def tyPred (param : ParamInfo) : TParser σ Pred := do
  let (TApp s l) <- tyArrow false param | error s!"not a valid predicate" *> throwUnexpected
  return ⟨s, l⟩
@[inline] def tyPreds (param : ParamInfo) : TParser σ (Array Pred) := sbrack $ sepBy1 COMMA $ tyPred param

def tyScheme : TParser σ Scheme := do
  let param@{ordered,..} <- optionD ((FORALL <|> FORALL') *> parseParams) ∅
  let pred <- optionD (tyPreds param) #[] <&> Array.toList
  if !ordered.isEmpty || !pred.isEmpty then COMMA
  .Forall (ordered.foldr (.cons ∘ .mkTV ∘ Prod.fst) []) pred <$> tyExp param

def tyRecord (tycon : String) (param : ParamInfo) (mt : Bool)
  : TParser σ TyDecl := withErrorMessage "TyRecord" do
  let fields <- sepBy COMMA (tyField mt param)
  let (fids, tys) := fields.unzip
  if fids.hasDuplicates id then
    error "duplicated fields not allowed in structure definition\n"
    throwUnexpected

  registerTy tycon param.ordered.size mt

  modify fun (st@{recordFields,..}, l) =>
    ({st with recordFields := recordFields.insert tycon fids}, l)
  return  { tycon
          , param := param.ordered
          , ctors := #[(tycon, fields.toList, tys.size)]}

def tyDecl (mt : Bool) : TParser σ TyDecl := withErrorMessage "TyDecl" do
  let cls? <- TYPE?
  let tycon <- ID
  if isUpperInit tycon then
    let param <- parseParams; EQ
    if <- test (kwOpExact "{") then
      let tydecl <- tyRecord tycon param mt <* kwOpExact "}"
      return {tydecl with cls?}
    else
      registerTy tycon param.ordered.size mt
      let hd <- (optional BAR *> ctor mt param)
      let tl <- takeMany (BAR *> ctor mt param)
      return {tycon, param := param.ordered, ctors := #[hd] ++ tl, cls?}

  else
    error "type constructor must begin with an uppercase letter\n"
    throwUnexpected
where
  ctor mt param := do
    let cname <- ID
    if isUpperInit cname then
      let args <- takeMany (parenthesized (tyForall mt param) <|> (tyForall mt param))
      let namedArgs := Prod.fst $ args.foldr (init := ([], 0)) fun s (a, i) =>
        ((s!"cname_{i}", s) :: a, i + 1)
      return (cname, namedArgs, args.size)
    else
      error "value constructor must begin with an uppercase letter\n"
      throwUnexpected

end PType

end Parsing
