import Tigris.TCNF.nflift

namespace TCNF.Opt open CC

/-!
# TCNF Optimization Pass

- Known-closure-call (from Claude).
  call statically known closure directly.

- DCE.
  removes dead let except for function application (unconditionally effectful for now).
  as well as any `Code.unreach` thus eliminating many fallback branches
  for complete pattern matrices.

- Constant Folding.
  collapses newtype/projection/single case analysis
  and folds projections on statically-known constructors.
-/


/-! ## Claude: Known-closure-call + arity (R1)

`app f args` / `pap f args` on a head `f` whose `(code, captured, remaining)` is
statically known becomes a direct call of the lifted `code` with the captured
args prepended (saturated), or a sharpened `pap` (still partial). Heads are known
when `f` is bound to a `mkClos`/`pap`, when `f` is a top-level `Decl` of known
arity, or when `f` is a top-level *value* decl that manifestly returns a partial
(R1: `let inc = add 1`). A following backward dead-`let` pass drops closures that
no longer escape, so non-escaping local functions — including (mutually)
recursive ones — collapse to direct calls with no allocation, while escaping
closures survive untouched.

Over-application whose tail arity is unknown (R2) is left to codegen's generic
apply; unknown heads (higher-order params) stay generic by design (see the
apply contract §1).
-/

abbrev AriMap  := Std.HashMap FVarId Nat
/-- head ↦ (code pointer, already-captured args, remaining caller arity). -/
abbrev ClosMap := Std.HashMap FVarId (FVarId × Array Atom × Nat)

/-- Resolve an application head: a known closure (`kc`), else a top-level decl of
known arity (`ari`, capturing nothing), else unknown. -/
@[inline] def resolveHead (ari : AriMap) (kc : ClosMap) (h : FVarId)
  : Option (FVarId × Array Atom × Nat) :=
  kc[h]? <|> (ari[h]?).map (h, #[], ·)

/-- Sharpen one `LetValue`: prepend a resolved head's captured args and
reclassify against its *remaining* arity. Returns the rewritten value plus an
optional `(code, captured, remaining)` entry to bind for the let's var so
downstream calls resolve. `mkClos` / partial `pap`/`app` yield an entry; a
saturated call does not (its result arity is R2). -/
def rewriteValue (ari : AriMap) (kc : ClosMap)
  : LetValue .postCC -> LetValue .postCC × Option (FVarId × Array Atom × Nat)
  | v@(.mkClos code env _) =>
    (v, (ari[code]?).bind fun k => if env.size <= k then some (code, env, k - env.size) else none)
  | .pap h args =>
    match resolveHead ari kc h with
    | some (code, cap, k) =>
      let cap := cap ++ args
      if args.size < k       then (.pap code cap, some (code, cap, k - args.size))
      else if args.size == k then (.app code cap, none)        -- exactly saturated ⇒ a call
      else                        (.pap code cap, none)         -- over via pap (unusual): keep merged
    | none => (.pap h args, none)
  | .app h args =>
    match resolveHead ari kc h with
    | some (code, cap, k) =>
      let cap := cap ++ args
      if args.size == k      then (.app code cap, none)         -- direct call
      else if args.size < k  then (.pap code cap, some (code, cap, k - args.size))
      else                        (.app h args, none)           -- over-app: leave to generic (R2)
    | none => (.app h args, none)
  | v => (v, none)

mutual
partial def koc (ari : AriMap) (kc : ClosMap) : CodePost -> CodePost
  | .let d k =>
    let (v, entry?) := rewriteValue ari kc d.value
    let kc := entry?.elim kc (kc.insert d.fvarId)
    .let {d with value := v} (koc ari kc k)
  | .jp d k           => .jp {d with body := koc ari kc d.body} (koc ari kc k)
  | .cases dc ty alts => .cases dc ty (alts.map (kocAlt ari kc))
  | c                 => c
partial def kocAlt (ari : AriMap) (kc : ClosMap) : Alt .postCC -> Alt .postCC
  | .ctor t ps k => .ctor t ps (koc ari kc k)
  | .const c k   => .const c (koc ari kc k)
  | .default k   => .default (koc ari kc k)
end

/-- The value a `Decl` body ultimately yields when it is a `…; let x = v in ret x`
tail — enough to see a value-decl's manifest `pap`/`mkClos`. -/
partial def retValue : CodePost -> Option (LetValue .postCC)
  | .let d (.ret (.fvar r)) => if r == d.fvarId then some d.value else none
  | .let _ k                => retValue k
  | _                       => none

/-- Get the linear let-spine of a decl body as a binding map. Used to resolve a value-decl's manifest closures. -/
def declBinds : CodePost -> Std.HashMap FVarId (LetValue .postCC)
  | .let d k => declBinds k |>.insert d.fvarId d.value
  | _        => ∅

/--
Resolve an atom captured by a _shared_ closure to a globally-valid one, or
none if it escapes as a decl-local. A decl-local empty-env `mkClos code` is just the
bare code pointer (both box to the same `clos`), so it resolves to `code`.
-/
def globalField (globals : FVSet) (binds : Std.HashMap FVarId (LetValue .postCC)) : Atom -> Option Atom
  | .fvar v =>
    if globals.contains v then some (.fvar v)
    else match binds[v]? with
      | some (.mkClos code env _) => if env.isEmpty then some (.fvar code) else none
      | _ => none
  | a => some a

/-- Module-wide seeds: each function decl's arity, plus every *value* decl that
manifestly returns a partial/closure, entered as a global closure so its uses
resolve to direct calls (R1). A shared entry's captures are resolved to globals
(`globalField`); a value decl capturing an unshareable local is left generic. -/
def seedMaps (globals : FVSet) (m : Module .postCC) : AriMap × ClosMap := Id.run do
  let all := m.decls.push m.main
  let mut ari : AriMap := ∅
  for d in all do
    if d.arity >= 1 then ari := ari.insert d.fvarId d.arity
  let mut gclos : ClosMap := ∅
  for d in all do
    if d.arity == 0 then
      if let some (code, cap, rem) := retValue d.body >>= Prod.snd ∘ (rewriteValue ari ∅ ·) then
        if let some cap := cap.mapM $ globalField globals $ declBinds d.body then
          gclos := gclos.insert d.fvarId (code, cap, rem)
  return (ari, gclos)

/-!
# Constant folding.

A forward pass that collapses newtype construction/projection/single case analysis
to identity, and folds projections on statically-known
constructors.
It is worth noting that this runs before KOC and works well with it as:

1. newtype variants collapse, in the case of dictionaries, to their method;
2. this allows KOC to pick them up as known heads, transforming
   exposed calls to become direct.

Note that `km` is seeded with top-level instance/record dictionaries
so monomorphic method projections resolve across functions.
-/

abbrev Subst := Std.HashMap FVarId Atom
inductive Known where
  | ctor (c : String) (fields : Array (Option Atom))    -- Optional since field may not be statically resolvable
  | pair (fst snd : Option Atom)
abbrev KMap := Std.HashMap FVarId Known

@[inline] def sa (σ : Subst) : Atom -> Atom
  | .fvar x => σ[x]?.getD (.fvar x)
  | a       => a
@[inline] def sfv (σ : Subst) (x : FVarId) : FVarId :=
  match σ[x]? with | some (.fvar y) => y | _ => x

def seedKM (globals : FVSet) (m : Module .postCC) : KMap := Id.run do
  let mut km : KMap := ∅
  for d in m.decls.push m.main do
    if d.arity == 0 then
      let binds := declBinds d.body
      match retValue d.body with
      | some (.ctor c as) =>
        km := km.insert d.fvarId $ .ctor c $ as.map $ globalField globals binds
      | some (.pair a b)  =>
        km := km.insert d.fvarId $ .pair (globalField globals binds a) (globalField globals binds b)
      | _ => pure ()
  return km

mutual
partial def cfold (nt : Std.HashSet String) (σ : Subst) (km : KMap) : CodePost -> CodePost
  | .let d k =>
    let cont (a : Atom) : CodePost :=                              -- fold `d` to atom `a`
      match a with
      | .lit l => .let {d with value := .lit l} $ cfold nt σ km k  -- a literal must stay a binding
      | a      => cfold nt (σ.insert d.fvarId a) km k              -- fvar/erased: copy-propagate
    match d.value with
    | .ctor c as =>
      let as := as.map (sa σ)
      if nt.contains c then cont $ as[0]?.getD .erased                          -- newtype: ctor is identity
      else .let {d with value := .ctor c as} $ cfold nt σ (km.insert d.fvarId (.ctor c (as.map some))) k
    | .field c i s =>
      let s := sfv σ s
      if nt.contains c then cont (.fvar s)                                      -- newtype: field is the value
      else match km[s]? with
        | some $ .ctor c' fs =>
          match if c' == c then fs[i]?.join else none with
          | some a => cont a                                                    -- known ctor: fold projection
          | none   => .let {d with value := .field c i s} $ cfold nt σ km k
        | _ => .let {d with value := .field c i s} $ cfold nt σ km k
    | .proj i s =>
      let s := sfv σ s
      match km[s]? with
      | some $ .pair a b =>
        match if i == 0 then a else b with
        | some x => cont x
        | none   => .let {d with value := .proj i s} $ cfold nt σ km k
      | _ => .let {d with value := .proj i s} $ cfold nt σ km k
    | .pair a b =>
      let a := sa σ a; let b := sa σ b
      .let {d with value := .pair a b} $ cfold nt σ (km.insert d.fvarId (.pair (some a) (some b))) k

    | .app h as     => .let {d with value := .app (sfv σ h) $ as.map $ sa σ} $ cfold nt σ km k
    | .pap h as     => .let {d with value := .pap (sfv σ h) $ as.map $ sa σ} $ cfold nt σ km k

    | .prim op as   => .let {d with value := .prim op   $ as.map $ sa σ} $ cfold nt σ km k
    | .extern nm as => .let {d with value := .extern nm $ as.map $ sa σ} $ cfold nt σ km k

    | .isCtor s t a => .let {d with value := .isCtor (sfv σ s) t a} $ cfold nt σ km k

    | .mkClos code env h => .let {d with value := .mkClos code (env.map (sa σ)) h} $ cfold nt σ km k

    | .lit l        => .let {d with value := .lit l} $ cfold nt σ km k

  | .jp d k => .jp {d with body := cfold nt σ km d.body} $ cfold nt σ km k
  | .cases dc ty alts =>
    let dc := sfv σ dc
    let altsC := alts.find? fun | .ctor c _ _ => nt.contains c | _ => false
    match altsC with
    | some $ .ctor _ ps k => -- newtype: no dispatch, field is the value
      match ps[0]? with
      | some p => cfold nt (σ.insert p.fvarId (.fvar dc)) km k
      | none   => cfold nt σ km k
    | _ => .cases dc ty $ alts.map $ cfoldAlt nt σ km
  | .jmp j as   => .jmp j $ as.map $ sa σ
  | .ret v      => .ret $ sa σ v
  | .unreach ty => .unreach ty
partial def cfoldAlt (nt : Std.HashSet String) (σ : Subst) (km : KMap) : Alt .postCC -> Alt .postCC
  | .ctor t ps k => .ctor t ps $ cfold nt σ km k
  | .const c k   => .const c   $ cfold nt σ km k
  | .default k   => .default   $ cfold nt σ km k
end

@[inline] def cfoldDecl (nt : Std.HashSet String) (km : KMap) (d : Decl .postCC) : Decl .postCC :=
  {d with body := cfold nt ∅ km d.body}

@[inline] def isPureV : LetValue φ -> Bool
  | .app .. | .extern .. => false   -- treat all foreign calls as effectful
  | _       => true

/-! Backward dead-pure-`let` (and unreachable join-point) elimination; returns
the cleaned code together with its free fvars. -/
mutual
partial def dceCode : CodePost -> CodePost × FVSet
  | .let d k =>
    let (k, u) := dceCode k
    if d.fvarId ∉ u && isPureV d.value then (k, u)
    else (.let d k, u.erase d.fvarId ∪ fvValue ∅ d.value)
  | .jp d k =>
    let (k, uk) := dceCode k
    if d.fvarId ∉ uk then (k, uk)  -- no `jmp` reaches it
    else
      let (body, ub) := dceCode d.body
      ( .jp {d with body} k
      , uk.erase d.fvarId
      ∪ d.params.foldl (·.erase ·.fvarId) ub)
  | .cases dc ty alts =>
    let alts := alts.map dceAlt
    (.cases dc ty (alts.map Prod.fst), alts.foldl (· ∪ ·.2) {dc})
  | .jmp j as   => (.jmp j as, fvAtoms ∅ as |>.insert j)
  | .ret v      => (.ret v, fvAtom ∅ v)
  | .unreach ty => (.unreach ty, ∅)
partial def dceAlt : Alt .postCC -> Alt .postCC × FVSet
  | .ctor t ps k =>
    let (k, u) := dceCode k; (.ctor t ps k, ps.foldl (·.erase ·.fvarId) u)
  | .const c k =>
    let (k, u) := dceCode k; (.const c k, u)
  | .default k =>
    let (k, u) := dceCode k; (.default k, u)
end

@[inline] def kocDecl (ari : AriMap) (gclos : ClosMap) (d : Decl .postCC) : Decl .postCC :=
  {d with body := dceCode (koc ari gclos d.body) |>.1}

end Opt
