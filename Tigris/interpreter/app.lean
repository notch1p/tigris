import Tigris.interpreter.eval

open Parsing PType Value MLType TV Pattern Expr TypingError Interpreter IO

namespace Parsing open Lexing Parser PType

def lpOrMod : TParser σ (Pattern × Expr ⊕ TopDecl) := withErrorMessage "Decl" $
  first' #[.inr <$> declaration, .inl <$> letPatDecl] simpErrorCombine

def lpOrModOrMut : TParser σ $ Array (Pattern × Expr ⊕ TopDecl) := do
  if <- test MUTUAL then
    mutTyDecl <* END
  else Array.singleton <$> lpOrMod

def toplevel : TParser σ $ Array (Pattern × Expr ⊕ TopDecl) := withErrorMessage "Toplevel" $ do
  let hd <- lpOrModOrMut <* optional END
  foldl (· ++ ·) hd (lpOrModOrMut <* optional END)

def parseModule (s : String) (PE : PEnv) (E : Env) (VE : VEnv) : EIO String (PEnv × Env × VEnv) :=
  match runST fun _ => toplevel <* spaces <* endOfInput |>.run s |>.run (PE, "") with
  | (.ok _ xs, (PE, l)) => do
    liftEIO (print l)
    xs.foldlM (init := (PE, E, VE)) fun (PE, E, VE) decl => do
      match decl with
      | .inl (pat, e) =>
        let (.Forall _ te, l) <- EIO.ofExcept $ runInfer1 e E |>.mapError toString
        liftEIO (print l)

        let ((tyacc, _, E), _, l) <- EIO.ofExcept $ (runEST fun _ => checkPat1 E te #[] pat |>.run (nat_lit 0, "")).mapError toString
        liftEIO (print l)

        let ex := Exhaustive.exhaustWitness E #[te] #[(#[pat], Expr.CUnit)]
        if let some ex := ex then
          liftEIO $ print $ Logging.warn
            s!"Partial pattern matching, \
               possible cases such as {ex.map (·.render)} are ignored\n"

        let v <- EIO.ofExcept $ eval VE e |>.mapError toString
        match evalPat1 v VE #[] pat with
        | some (VE, vacc) =>
          for ty in tyacc, (sym, val) in vacc do
            liftEIO $ println $ templateREPL sym val.render ty.render
          return (PE, E, VE)
        | none => throw $ NoMatch #[e] v.render #[(#[pat], Expr.CUnit)] |> toString
      | .inr b =>
        match b with
        | .inl (id, expr) =>
          let (ty, l) <- ofExcept $ runInfer1 expr E |>.mapError toString
          liftEIO (print l)
          let v <- ofExcept $ eval VE expr |>.mapError toString
          liftEIO $ println $ templateREPL id v.render ty.render
          return (PE, ⟨E.1.insert id ty, E.2⟩, ⟨VE.env.insert id v⟩)
        | .inr tydecl =>
          (PE, ·) <$> registerData E VE tydecl
  | (.error _ e, (_, l)) => liftEIO (print l) *> throw (toString e)

end Parsing

def evalToplevel (bs : Array Binding) (VE : VEnv) : Except TypingError VEnv :=
  bs.foldlM (init := VE) fun VE@⟨env⟩ (id, e) => (VEnv.mk ∘ env.insert id) <$> eval VE e

def interpret PE E VE s := parseModule s PE E VE |>.toIO userError
