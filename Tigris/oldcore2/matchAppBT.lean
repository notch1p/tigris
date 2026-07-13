/-! backtracking automata, not actually used.
import Tigris.coreL.lam
namespace IR
partial def lowerRowK
  (scrs : Array Name) (pats : Array Pattern) (ρ : Env)
  (rhs : Expr) (k : Name -> M σ LExpr) (onFail : LExpr)
  : M σ LExpr := go 0 scrs pats ρ where
  go i scrs pats ρ :=
    if h : i < pats.size then
      let s := scrs[i]!
      match pats[i] with
      | .PWild => go i.succ scrs pats ρ
      | .PVar x => .letVal x (.var s) <$> go i.succ scrs pats (ρ.insert x x)
      | .PConst tc => do
        let (ck, op) := constOf tc
        let cv <- fresh "c"
        let cmp <- fresh "cmp"
        let tBranch <- go i.succ scrs pats ρ
        pure ∘ .letVal cv (.cst ck) ∘ .letRhs cmp (.prim op #[s, cv]) $
          .seq #[] (.cond cmp tBranch onFail)
      | .PProd' p q => do
        let l <- fresh "l"; let r <- fresh "r"
        let (scrs, pats) := (scrs.replaceAt i #[l, r], pats.replaceAt i #[p, q])
        .letRhs l (.proj s 0) <$> (.letRhs r (.proj s 1)) <$> go i scrs pats ρ
      | .PCtor cname args => do
        let flag <- fresh "is"
        let fcount := args.size
        let fNames := Array.ofFn (fun i => s!"f{i}") (n := fcount)
        let scrs := scrs.replaceAt i fNames
        let pats := pats.replaceAt i args
        let tCont <- go i scrs pats ρ
        let tBranch := fcount.foldRev (init := tCont)
          fun i _ a => .letRhs s!"f{i}" (.proj s i) a
        return .letRhs flag (.isConstr s cname fcount) $
          .seq #[] (.cond flag tBranch onFail)

    else lowerE rhs ρ k

partial def lowerMatchBT
  (scrs : Array Name) (rows : Array (Array Pattern × Expr))
  (ρ : Env) (k : Name -> M σ LExpr) : M σ LExpr := do
  let u <- fresh "u"
  let kont <- k u
  let fallback : LExpr := .letVal u (.cst .unit) kont
  rows.foldrM (uncurry $ (lowerRowK scrs · ρ · k ·)) fallback
end IR
-/
