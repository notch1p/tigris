import Tigris.interpreter.eval

open Parsing PType Value MLType TV Pattern Expr TypingError Interpreter IO Std.ToFormat

namespace Parsing open Lexing Parser PType

def parseModule (s : String) (PE : PEnv) (E : Env) (VE : VEnv) : EIO String (PEnv × Env × VEnv) :=
  match runST fun _ => toplevel <* spaces <* endOfInput |>.run s |>.run (PE, "") with
  | (.ok _ xs, (PE, l)) => do
    liftEIO (print l)
    xs.foldlM (init := (PE, E, VE)) fun (PE, E, VE) decl => do
      match decl with
      | .patBind (pat, e) =>
        let (.Forall _ te, l) <- EIO.ofExcept $ runInfer1 e E |>.mapError toString
        liftEIO (print l)

        let ((tyacc, _, E), _, l) <- EIO.ofExcept $ (runEST fun _ => checkPat1 E te #[] pat |>.run (nat_lit 0, "")).mapError toString
        liftEIO (print l)
        -- toplevel binding can never be redundant
        let (ex, _, _) := Exhaustive.exhaustWitness E #[te] #[(#[pat], Expr.CUnit)]
        if let some ex := ex then
          liftEIO $ print $ Logging.warn
            s!"Partial pattern matching, \
               possible cases such as {ex.map (·.render)} are ignored\n"

        let v <- EIO.ofExcept $ eval VE e |>.mapError toString
        match evalPat1 v VE #[] pat with
        | some (VE, vacc) =>
          for ty in tyacc, (sym, val) in vacc do
            liftEIO $ println $ templateREPL sym (format val) (format ty)
          return (PE, E, VE)
        | none => throw $ NoMatch #[e] (format v).pretty #[(#[pat], Expr.CUnit)] |> toString
      | .idBind group =>
        let (ty, E, l) <- ofExcept $ inferGroup group E "" |>.mapError toString
        liftEIO (print l)
        let vs <- group.mapM fun (id, expr) =>
          (id, ·) <$> (EIO.ofExcept $ eval VE expr |>.mapError toString)
        for (id, ty) in ty, (_, v) in vs do
          liftEIO $ println $ templateREPL id (format v) (format ty)
        let VE := vs.foldl (init := VE.env) fun acc (id, v) => acc.insert id v
        return (PE, E, ⟨VE⟩)
      | .tyBind tydecl =>
        (PE, ·) <$> registerData E VE tydecl
  | (.error _ e, (_, l)) => liftEIO (print l) *> throw (toString e)

end Parsing

def evalToplevel (bs : Array Binding) (VE : VEnv) : Except TypingError VEnv :=
  bs.foldlM (init := VE) fun VE@⟨env⟩ (id, e) => (VEnv.mk ∘ env.insert id) <$> eval VE e

def interpret PE E VE s := parseModule s PE E VE |>.toIO userError
