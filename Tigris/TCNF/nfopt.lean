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

-/


/-! ## Claude: Known-closure-call optimization

`app f args` / `pap f args` where `f := 𝐂⟦code, env⟧` is a statically-known
closure becomes a direct call of the lifted `code`, prepending the captured
`env`. A following backward dead-`let` pass drops closures that no longer escape
(and any other dead pure let), so non-escaping local functions — including
(mutually) recursive ones — collapse to direct calls with no allocation, while
escaping closures survive untouched.
-/

abbrev ClosMap := Std.HashMap FVarId (FVarId × Array Atom)

mutual
partial def koc (kc : ClosMap) : CodePost -> CodePost
  | .let d k =>
    match d.value with
    | .mkClos code env _ => .let d $ koc (kc.insert d.fvarId (code, env)) k
    | .app h args =>
      match kc[h]? with
      | some (code, env) => .let {d with value := .app code (env ++ args)} $ koc kc k
      | none             => .let d $ koc kc k
    | .pap h args =>
      match kc[h]? with
      | some (code, env) => .let {d with value := .pap code (env ++ args)} $ koc kc k
      | none             => .let d $ koc kc k
    | _ => .let d $ koc kc k
  | .jp d k           => .jp {d with body := koc kc d.body} $ koc kc k
  | .cases dc ty alts => .cases dc ty $ alts.map (kocAlt kc)
  | c => c
partial def kocAlt (kc : ClosMap) : Alt .postCC -> Alt .postCC
  | .ctor t ps k => .ctor t ps $ koc kc k
  | .const c k   => .const c $ koc kc k
  | .default k   => .default $ koc kc k
end

@[inline] def isPureV : LetValue φ -> Bool
  | .app .. => false
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

@[inline] def kocDecl (d : Decl .postCC) : Decl .postCC :=
  {d with body := dceCode (koc ∅ d.body) |>.1}

end Opt
