import Tigris.interpreter.eval

open Parsing PType Value MLType TV Pattern Expr TypingError Interpreter IO

def evalToplevel (bs : Array Binding) (VE : VEnv) : Except TypingError VEnv :=
  bs.foldlM (init := VE) fun VE@⟨env⟩ (id, e) => (VEnv.mk ∘ env.insert id) <$> eval VE e

def interpret (PE : PEnv) (E : Env) (VE : VEnv) (s : String) : IO (PEnv × Env × VEnv) := do
  match parseModule s PE with
  | .ok bs PE =>
    bs.foldlM (init := (PE, E, VE)) fun (PE, E, ve@{env := VE}) b => do
      match b with
      | .inl (id, expr) =>
        let ty <- IO.ofExcept $ runInfer1 expr E |>.mapError toString
        let v <- IO.ofExcept $ eval ve expr |>.mapError toString
        println s!"{id} : {v} |- {ty.1}"
        print ty.2
        return (PE, ⟨E.1.insert id ty.1, E.2⟩, ⟨VE.insert id v⟩)
      | .inr tydecl =>
        (PE, ·) <$> registerData E ve tydecl
  | .error e _ => IO.throwServerError e
