import Tigris.cps.cps

namespace CPS
def occursVarCRhs (x : CName) : CRhs -> Bool
  | .prim _ args => args.any (· == x)
  | .proj s _  => s == x
  | .mkPair a b => a == x || b == x
  | .mkConstr _ fs => fs.any (· == x)
  | .isConstr s _ _ => s == x
  | .const _ => false
  | .alias y => y == x

mutual
partial def occursVarCTail (x : CName) : CTail -> Bool
  | .appFun f p k => f == x  || p == x || k == x
  | .appKont k v => k == x || v == x
  | .ite c t e => c == x || occursVarCExpr x t || occursVarCExpr x e
  | .switchConst s cs d? =>
    s == x || cs.any (occursVarCExpr x ∘ Prod.snd) || d?.any (occursVarCExpr x)
  | .switchCtor s ar d? =>
    s == x || ar.any (occursVarCExpr x ∘ Prod.snd ∘ .snd) || d?.any (occursVarCExpr x)
  | .halt v => v == x
partial def occursVarCExpr (x : CName) : CExpr -> Bool
  | .let1 y rhs b =>
    occursVarCRhs x rhs || if y == x then false else occursVarCExpr x b
  | .letKont kid param kbody body =>
    if kid == x || param == x then false
    else occursVarCExpr x kbody || occursVarCExpr x body
  | .letRec funs body =>
    let matcher | ⟨f, p, k, _⟩ => f == x || p == x || k == x
    let bodyShadow := funs.any matcher
    let funBodies := funs.any fun f =>
      if matcher f then false else occursVarCExpr x f.body
    (if bodyShadow then false else occursVarCExpr x body) || funBodies
  | .tail t => occursVarCTail x t
end

partial def occursKontUse (k : CName) : CExpr -> Bool
  | .let1 _ rhs b =>
    occursVarCRhs k rhs || occursKontUse k b
  | .letKont kid _ kbody body =>
    if kid == k then false else occursKontUse k kbody || occursKontUse k body
  | .letRec funs body =>
    occursKontUse k body || funs.any (occursKontUse k ∘ CFun.body)
  | .tail t =>
    match t with
    | .appFun _ _ k' => k' == k
    | .appKont k' _ => k' == k
    | .ite _ t e => occursKontUse k t || occursKontUse k e
    | .switchConst _ cs d? =>
      cs.any (occursKontUse k ∘ Prod.snd) || d?.any (occursKontUse k)
    | .switchCtor _ ar d? =>
      ar.any (occursKontUse k ∘ Prod.snd ∘ .snd) || d?.any (occursKontUse k)
    | .halt _ => false

partial def replaceKont (kOld kNew : CName) : CExpr -> CExpr
  | .let1 x rhs b =>
    .let1 x rhs (replaceKont kOld kNew b)
  | .letKont kid param kbody body =>
    if kid == kOld then
      .letKont kid param kbody body
    else
      .letKont kid param (replaceKont kOld kNew kbody) (replaceKont kOld kNew body)
  | .letRec funs body =>
    .letRec (funs.map (fun f => {f with body := replaceKont kOld kNew f.body}))
            (replaceKont kOld kNew body)
  | .tail t =>
    let t' :=
      match t with
      | .appFun f p k        => .appFun f p (if k == kOld then kNew else k)
      | .appKont k v         => .appKont (if k == kOld then kNew else k) v
      | .ite c t e           => .ite c (replaceKont kOld kNew t) (replaceKont kOld kNew e)
      | .switchConst s cs d? => .switchConst s
                                  (cs.map (fun (k, b) => (k, replaceKont kOld kNew b)))
                                  (d?.map (replaceKont kOld kNew))
      | .switchCtor s cs d?  => .switchCtor s
                                  (cs.map (fun (c, ar, b) => (c, ar, replaceKont kOld kNew b)))
                                  (d?.map (replaceKont kOld kNew))
      | .halt v              => .halt v
    .tail t'

partial def inlineTrivialKont : CExpr -> CExpr
  | .let1 x rhs b =>
    .let1 x rhs (inlineTrivialKont b)
  | .letKont kid param kbody body =>
    match kbody with
    | .tail (.appKont k' v) =>
      if v == param then
        let body' := replaceKont kid k' body
        inlineTrivialKont body'
      else
        .letKont kid param (inlineTrivialKont kbody) (inlineTrivialKont body)
    | _ =>
      .letKont kid param (inlineTrivialKont kbody) (inlineTrivialKont body)
  | .letRec funs body =>
    .letRec (funs.map (fun f => {f with body := inlineTrivialKont f.body}))
            (inlineTrivialKont body)
  | .tail t =>
    let t' :=
      match t with
      | .ite c t e           => .ite c (inlineTrivialKont t) (inlineTrivialKont e)
      | .switchConst s cs d? =>
        .switchConst s
          (cs.map (fun (k, b) => (k, inlineTrivialKont b)))
          (d?.map inlineTrivialKont)
      | .switchCtor s cs d?  =>
        .switchCtor s
          (cs.map (fun (c, ar, b) => (c, ar, inlineTrivialKont b)))
          (d?.map inlineTrivialKont)
      | _ => t
    .tail t'

partial def substVarCPS (x y : CName) : CExpr -> CExpr
  | .let1 z rhs b =>
    let rhs' :=
      match rhs with
      | .prim op args    => .prim op (args.map (fun a => if a == x then y else a))
      | .proj s i        => .proj (if s == x then y else s) i
      | .mkPair a b      => .mkPair (if a == x then y else a) (if b == x then y else b)
      | .mkConstr t fs   => .mkConstr t (fs.map (fun a => if a == x then y else a))
      | .isConstr s t ar => .isConstr (if s == x then y else s) t ar
      | .const k         => .const k
      | .alias a         => .alias (if a == x then y else a)
    if z == x then
      .let1 z rhs' b
    else
      .let1 z rhs' (substVarCPS x y b)
  | .letKont kid param kbody body =>
    let kbody' := if param == x then kbody else substVarCPS x y kbody
    let body'  := if kid == x then body else substVarCPS x y body
    .letKont kid param kbody' body'
  | .letRec funs body =>
    let funs' := funs.map (fun f =>
      let shadow := (f.fid == x) || (f.payloadParam == x) || (f.kontParam == x)
      {f with body := (if shadow then f.body else substVarCPS x y f.body)})
    let body' := substVarCPS x y body
    .letRec funs' body'
  | .tail t =>
    let t' :=
      match t with
      | .appFun f p k =>
        .appFun (if f == x then y else f)
                (if p == x then y else p)
                (if k == x then y else k)
      | .appKont k v =>
        .appKont (if k == x then y else k)
                 (if v == x then y else v)
      | .ite c t e =>
        .ite (if c == x then y else c)
             (substVarCPS x y t)
             (substVarCPS x y e)
      | .switchConst s cs d? =>
        .switchConst (if s == x then y else s)
                     (cs.map (fun (k, b) => (k, substVarCPS x y b)))
                     (d?.map (substVarCPS x y))
      | .switchCtor s cs d? =>
        .switchCtor (if s == x then y else s)
                    (cs.map (fun (c, ar, b) => (c, ar, substVarCPS x y b)))
                    (d?.map (substVarCPS x y))
      | .halt v => .halt (if v == x then y else v)
    .tail t'

partial def dceCExpr : CExpr -> CExpr
  | .let1 x (.alias y) b => dceCExpr (substVarCPS x y b)
  | .let1 x rhs b =>
    let b' := dceCExpr b
    if occursVarCExpr x b' then
      .let1 x rhs b'
    else b'
  | .letKont kid param kbody body =>
    let kbody' := dceCExpr kbody
    let body'  := dceCExpr body
    if occursKontUse kid body' then
      .letKont kid param kbody' body'
    else body'
  | .letRec funs body =>
    let funs' := funs.map (fun f => {f with body := dceCExpr f.body})
    .letRec funs' (dceCExpr body)
  | .tail t =>
    let t' :=
      match t with
      | .ite c t e => .ite c (dceCExpr t) (dceCExpr e)
      | .switchConst s cs d? =>
        .switchConst s
          (cs.map (fun (k, b) => (k, dceCExpr b)))
          (d?.map dceCExpr)
      | .switchCtor s cs d?  =>
        .switchCtor s
          (cs.map (fun (c, ar, b) => (c, ar, dceCExpr b)))
          (d?.map dceCExpr)
      | _ => t
    .tail t'

def optimizeCExpr (e : CExpr) : CExpr :=
  let e1 := inlineTrivialKont e
  dceCExpr e1
def optimizeCFun (f : CFun) : CFun :=
  {f with body := optimizeCExpr f.body}

def optimizeCModule (m : CModule) : CModule :=
  {m with funs := m.funs.map optimizeCFun, main := optimizeCFun m.main}
end CPS
