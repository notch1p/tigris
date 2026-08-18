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

def getTyFlag (name : String) : TParser σ $ Option Bool := do
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

/-- kind mv, denoted ?k.{n}. it is to be constrained by kind inference. -/
def freshKV : TParser σ Kind := do
  let n <- modifyGet fun (pe@{nxtK,..}, s) => (nxtK, ({pe with nxtK := nxtK + 1}, s))
  return .kvar n

def parseKV : TParser σ (String × Kind) := ID >>= fun id => (id, ·) <$> freshKV

def parseParam : TParser σ (String × Kind) := parseKV <? parenthesized do
  let id <- ID
  if <- test COLON then
    spaces
    let k <- parseKind
    pure (id, k)
  else (id, ·) <$> freshKV

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

def registerTy (name : String) (mt : Bool) (flag := true) : TParser σ Unit := do
  if <- modifyGet fun orig@(st@{tys,..}, l) =>
    match tys.find? name with
    | none =>
      (true, {st with tys := tys.insert name flag}, l)
    | some k =>
      if mt then
        if !k && flag then (true, {st with tys := tys.insert name flag}, l)
        else (true, orig)
      else
        let err := Logging.error
          s!"types are dynamically scoped: for this reason {name} may not be redefined.\n"
        (false, st, l ++ err)
  then return ()
  else throwUnexpected

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
    | some _ => return TVar (.named id)
    | none =>
      error s!"unbound type variable {id}\n"
      throwUnexpected

partial def tyApps (mt : Bool) (param : ParamInfo) : TParser σ MLType := withExpected "type term" do
  let hd <- tyAtom mt param
  match hd with
  | .TCon h =>
    match <- getTyFlag h with
    | some _ => .mkApp (.TCon h) <$> Array.toList <$> takeMany (tyAtom mt param) -- btype
    | none =>
      if mt then -- Forward reference
        modify fun (pe@{undTy,..}, s) => ({pe with undTy := h :: undTy}, s)
        let args <- takeMany $ tyAtom mt param
        registerTy h mt false
        return .mkApp (.TCon h) args.toList
      else error s!"undefined type {h}\n"; throwUnexpected
  | .TVar v => .mkApp (.TVar v) <$> Array.toList <$> takeMany (tyAtom mt param)
  | _ => return hd

partial def tyProd (mt : Bool) (param : ParamInfo) : TParser σ MLType := do
  let t₁ <- tyApps mt param
  let tn <- takeMany (ws (char '×' <|> char '*') *> tyApps mt param)
  return (t₁ :: tn.toList).foldr1 TProd (List.cons_ne_nil _ _)

partial def tyArrow (mt : Bool) (param : ParamInfo) : TParser σ MLType := do
  let lhs <- tyProd mt param
  (ARROW *> tyArrow mt param >>= fun rhs => pure $ TArr lhs rhs) <|> pure lhs

/-- Nested forall (rank-n): binders only. only the outermost tyforall can have predicates. -/
partial def tyForallN (mt : Bool) (param : ParamInfo) : TParser σ MLType :=
  (optionD ((FORALL <|> FORALL') *> parseParams) ∅) >>= fun param' =>
    if param'.ordered.isEmpty then tyCtor param <|> parenthesized (tyArrow mt param)
    else do
      let param := param ∪ param'; COMMA
      .TSch <$> .Forall (param'.ordered.foldr (.cons ∘ .named ∘ Prod.fst) []) [] <$> tyArrow mt param

partial def tyAtom (mt : Bool) (param : ParamInfo) : TParser σ MLType := tyForallN mt param
end

def tyEmpty : TParser σ TyDecl := do
  TYPE let tycon <- ID let {ordered,..} <- parseParams;
  return {tycon, param := ordered.map fun (n, k) => (.named n, k), ctors := #[]}

@[inline, always_inline]
def tyExp (paramInfo : ParamInfo := ∅) : TParser σ MLType := tyArrow false paramInfo

def tyPred (param : ParamInfo) : TParser σ Pred := do
  let ty <- tyArrow false param
  match ty with
  | .TApp (.TCon s) l => return ⟨s, l⟩
  | .TCon s           => return ⟨s, []⟩
  | _ => error s!"not a valid predicate" *> throwUnexpected
@[inline] def tyPreds (param : ParamInfo) : TParser σ (Array Pred) := sbrack $ sepBy1 COMMA $ tyPred param

def tyForall (mt : Bool) (param : ParamInfo) : TParser σ MLType := do
  let param'@{ordered,..} <- optionD ((FORALL <|> FORALL') *> parseParams) ∅
  let param := param ∪ param'
  let pred <- optionD (tyPreds param) #[] <&> Array.toList
  if ordered.isEmpty && pred.isEmpty then tyArrow mt param
  else
    COMMA
    .TSch <$> .Forall (ordered.foldr (.cons ∘ .named ∘ Prod.fst) []) pred <$> tyArrow mt param

def tyField (mt : Bool) (param : ParamInfo) : TParser σ (Symbol × MLType) := do
  let id <- ID; COLON; let ty <- tyForall mt param
  return (id, ty)

def tyScheme : TParser σ Scheme := do
  let param@{ordered,..} <- optionD ((FORALL <|> FORALL') *> parseParams) ∅
  let pred <- optionD (tyPreds param) #[] <&> Array.toList
  if !ordered.isEmpty || !pred.isEmpty then COMMA
  .Forall (ordered.foldr (.cons ∘ .named ∘ Prod.fst) []) pred <$> tyExp param

def tyInstScheme : TParser σ (Scheme × ParamInfo) := do
  let param@{ordered,..} <- optionD ((FORALL <|> FORALL') *> parseParams) ∅
  let pred <- optionD (tyPreds param) #[] <&> Array.toList
  if !ordered.isEmpty || !pred.isEmpty then COMMA
  (·, param) <$> .Forall (ordered.foldr (.cons ∘ .named ∘ Prod.fst) []) pred <$> tyExp param

def tyRecord (tycon : String) (param : ParamInfo) (mt : Bool) (offside? : Bool)
  : TParser σ TyDecl := withExpected "structure declaration" do
  let fields <-
    if offside? then alignedBindings (tyField mt param)
    else sepBy COMMA (tyField mt param)
  let (fids, tys) := fields.unzip
  if fids.hasDuplicates id then
    error "duplicated fields not allowed in structure definition\n"
    throwUnexpected

  registerTy tycon mt

  modify fun (st@{recordFields,..}, l) =>
    ({st with recordFields := recordFields.insert tycon fids}, l)
  return  { tycon
          , param := param.ordered.map fun (n, k) => (.named n, k)
          , ctors := #[(tycon, fields.toList, tys.size)]}

def tyDecl (mt : Bool) : TParser σ TyDecl := withExpected "type declaration" do
  let cls? <- TYPE?
  let tycon <- ID
  if tycon.isUpperInit then
    let param <- parseParams;
    first
      [ EQ *> do
          if <- test (kwOpExact "{") then
            let tydecl <- tyRecord tycon param mt false <* kwOpExact "}"
            return {tydecl with cls?}
          else
            registerTy tycon mt
            let hd <- (optional BAR *> ctor mt param)
            let tl <- takeMany (BAR *> ctor mt param)
            return {tycon, param := param.ordered.map fun (n, k) => (.named n, k), ctors := #[hd] ++ tl, cls?}
      , WHERE *> tyRecord tycon param mt true <&> fun tydecl => {tydecl with cls?}
      , registerTy tycon mt *>
        pure {tycon, param := param.ordered.map fun (n, k) => (.named n, k), ctors := {}}
      ]

  else
    error "type constructor must begin with an uppercase letter\n"
    throwUnexpected
where
  ctor mt param := do
    let cname <- ID
    if cname.isUpperInit then
      -- atype
      let args <- takeMany (parenthesized (tyForall mt param) <|> tyAtom mt param)
      let (namedArgs, _) := args.foldr (fun s (a, i) => ((s!"cname_{i}", s) :: a, i + 1)) ([], 0)
      return (cname, namedArgs, args.size)
    else
      error "value constructor must begin with an uppercase letter\n"
      throwUnexpected

/-- recursive abbreviation is a parse error. -/
def tySyn : TParser σ TyDecl := withExpected "type abbreviation" do
  ABBREV
  let tycon <- ID
  if tycon.isUpperInit then
    let param <- parseParams; EQ
    let rhs <- tyExp param -- tyExp checks for unbound types
    registerTy tycon false
    return { tycon, param := param.ordered.map fun (n, k) => (.named n, k), ctors := #[], rhs := some rhs }
  else
    error "type constructor must begin with an uppercase letter\n"
    throwUnexpected

end PType

end Parsing
