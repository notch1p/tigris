import Tigris.interpreter.eval

open Parsing PType Value MLType TV Pattern Expr TypingError Interpreter IO

namespace Parsing open Lexing Parser PType

def lpOrMod : TParser σ (Pattern × Expr ⊕ TopDecl) := first' #[.inr <$> declaration, .inl <$> letPatDecl]

def toplevel : TParser σ $ Array (Pattern × Expr ⊕ TopDecl) := 
  sepBy (optional END) lpOrMod <* optional END

def parseModule (s : String) (PE : PEnv) (E : Env) (VE : VEnv) : EIO String (PEnv × Env × VEnv) :=
  match runST fun _ => Lexing.spaces *> toplevel <* endOfInput |>.run s |>.run (PE, "") with
  | (.ok _ xs, (PE, l)) => do
    liftEIO (print l)
    xs.foldlM (init := (PE, E, VE)) fun (PE, E, VE) decl => do
      match decl with
      | .inl (pat, e) =>
        let (.Forall _ te, l) <- EIO.ofExcept $ runInfer1 e E |>.mapError toString
        liftEIO (print l)

        let ((_, E), _, l) <- EIO.ofExcept $ (runEST fun _ => checkPat1 E te pat |>.run (nat_lit 0, "")).mapError toString
        liftEIO (print l)

        let ex := Exhaustive.exhaustWitness E #[te] #[(#[pat], Expr.CUnit)]
        if let some ex := ex then
          liftEIO $ print $ Logging.warn
            s!"Partial pattern matching i.e. \
               possible cases such as {Logging.cyan $ toString ex} are ignored\n"

        let v <- EIO.ofExcept $ eval VE e |>.mapError toString
        match evalPat1 v VE #[] pat with
        | some (VE, acc) =>
          if h : acc.size > 0 then
            let (sym, val) := acc.mapReduce (Prod.map toString (·.render)) (h := h) fun (asym, aval) (sym, val) =>
              (s!"{asym},{sym}", s!"{aval}, {val}")
            liftEIO $ println $ templateREPL sym val te.render
          return (PE, E, VE)
        | none    => throw $ NoMatch #[e] v.render #[(#[pat], Expr.CUnit)] |> toString
      | .inr b =>
        match b with
        | .inl (id, expr) =>
          let (ty, l) <- ofExcept $ runInfer1 expr E |>.mapError toString
          liftEIO (print l)
          let v <- ofExcept $ eval VE expr |>.mapError toString
          liftEIO $ println $ templateREPL id v.render ty.render
          return (PE, ⟨E.1.insert id ty, E.2⟩, ⟨VE.env.insert id v⟩)
        | .inr tydecl =>
          (PE, ·) <$> liftEIO (registerData E VE tydecl)
  | (.error _ e, (_, l)) => liftEIO (print l) *> throw (toString e)


end Parsing

def evalToplevel (bs : Array Binding) (VE : VEnv) : Except TypingError VEnv :=
  bs.foldlM (init := VE) fun VE@⟨env⟩ (id, e) => (VEnv.mk ∘ env.insert id) <$> eval VE e

def interpret PE E VE s := parseModule s PE E VE |>.toIO $ userError ∘ Logging.error

