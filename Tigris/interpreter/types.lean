import Tigris.parsing.types

mutual
structure VEnv where
  env : Std.HashMap.Raw String Value

inductive Value where
  | VI (i : Int) | VB (b : Bool) | VS (s : String) | VU
  | VF (s : Symbol) (E : Expr) (e : VEnv)
  | VFRec (s: Symbol) (e : Expr) (E : VEnv)
  | VOpaque (s : Nat)
  | VEvalError (s : String)
  | VP (e₁ e₂ : Value) 
  | VCtor (name : String) (arity : Nat) (acc : Array Value)
  | VConstr (name : String) (fields : Array Value)
  deriving Nonempty
end
instance : Inhabited Value := ⟨.VEvalError "something wrong during evaluation.\n\
                                            Note: Likely implementation error or a breach of type safety\n\
                                            Note: The type system is unsound by design\n\
                                            Note: because the primitive `rec` fixpoint combinator is present\n"⟩
def Value.toStr : Value -> String
  | VI v | VB v => toString v | VU => toString ()
  | VS v => reprStr v
  | VEvalError s => s
  | VOpaque s   => s!"<${s}::prim>"
  | VF _ _ _    => "<fun>"
  | VFRec _ _ _ => "<recfun>"
  | VCtor n k acc => s!"<{n}/{k}{acc.foldl (· ++ " " ++ toStr ·) ""}::ctor>"
  | VConstr n fs => fs.foldl (· ++ " " ++ toStr ·) n
  | VP v₁ v₂    => paren (prod? v₁) (toStr v₁) ++ "," ++ toStr v₂ where
    paren b s := bif b then s!"({s})" else s
    prod? | VP _ _ => true | _ => false
instance : ToString Value := ⟨Value.toStr⟩

