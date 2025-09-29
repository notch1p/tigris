import Tigris.interpreter.eval

open Parsing PType Value MLType TV Pattern Expr TypingError Interpreter IO Std.ToFormat

abbrev CtorMap := Std.HashMap String Nat
namespace Parsing open Lexing Parser PType
def parseModule (s : String) (PE : PEnv) (E : Env) (VE : VEnv)
  (ctors : CtorMap) : EIO String (CtorMap × PEnv × Env × VEnv) :=
  match runST fun _ => toplevel <* spaces <* endOfInput |>.run s |>.run (PE, "") with
  | (.ok _ xs, (PE, l)) => do
    liftEIO (print l)
    xs.foldlM (init := (ctors, PE, E, VE)) fun (ctors, PE, E, VE) decl => do
      match decl with
      | .extBind id _ sch =>
        let E := {E with E := E.E.insert id sch}
        liftEIO (print ∘ Logging.warn $ "`extern` definition only updates the typing environment in REPL:\n\
                                         It's not used for evaluation. This can been seen as importing an axiom.\n")
        $> (ctors, PE, E, VE)
      | .patBind (pat, e) =>
        let (.Forall _ _ te, l) <- EIO.ofExcept $ runInfer1 e E |>.mapError toString
        liftEIO (print l)

        let ((tyacc, _, E), _, l) <- EIO.ofExcept $ (runEST fun _ => checkPat1 E te #[] pat |>.run (nat_lit 0, "")).mapError toString
        liftEIO (print l)
        -- toplevel binding can never be redundant
        let (ex, _, _) := Exhaustive.exhaustWitness E #[te] #[(#[pat], Expr.CUnit)]
        if let some ex := ex then
          liftEIO $ print $ Logging.warn
            s!"Partial pattern matching, an unmatched candidate is\
             \n  {ex.map (·.render)}\n"

        let v <- evalC VE e |>.adaptExcept toString
        match evalPat1 v VE #[] pat with
        | some (VE, vacc) =>
          for ty in tyacc, (sym, val) in vacc do
            liftEIO $ println $ templateREPL sym (format val) (format ty)
          return (ctors, PE, E, VE)
        | none => throw $ NoMatch #[e] (format v).pretty #[(#[pat], Expr.CUnit)] |> toString
      | .idBind group =>
        let (ty, E, l) <- ofExcept $ inferGroup group E "" |>.mapError toString
        liftEIO (print l)
        let (recBinds, nonrecBinds) := group.partition $ MLType.isRecRhs ∘ Prod.snd
        let recVal <- recBinds.mapM fun (id, expr) => (id, ·) <$> (evalC VE expr |>.adaptExcept toString)
        let VE := recVal.foldl (init := VE.env) fun acc (id, v) => acc.insert id v
        let (nonrecVal, VE) <- nonrecBinds.foldlM (init := (#[], VE)) fun (acc, VE) (id, expr) => do
          let v <- evalC ⟨VE⟩ expr |>.adaptExcept toString
          return (acc.push (id, v), VE.insert id v)
        for (id, ty) in ty, (_, v) in nonrecVal ++ recVal do
          liftEIO $ println $ templateREPL id (format v) (format ty)
        return (ctors, PE, E, ⟨VE⟩)
      | .tyBind tydecl =>
        let ctors := ctors.insertMany $ tydecl.ctors.map fun (name, _, ar) => (name, ar)
        (ctors, PE, ·) <$> registerData E VE tydecl
  | (.error _ e, (_, l)) => liftEIO (print l) *> throw (toString e)

end Parsing

def evalToplevel (bs : Array Binding) (VE : VEnv) : Except TypingError VEnv :=
  bs.foldlM (init := VE) fun VE@⟨env⟩ (id, e) => (VEnv.mk ∘ env.insert id) <$> eval VE e

def interpret PE E VE s ctors := parseModule s PE E VE ctors |>.toIO userError
