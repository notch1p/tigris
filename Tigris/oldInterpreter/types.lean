import Tigris.parsing.types
import Tigris.utils

mutual
structure VEnv where
  env : Std.TreeMap.Raw String Value
deriving Repr

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

instance : Inhabited Value := ⟨.VEvalError $ "something wrong during evaluation.\n"
                                          ++ Logging.note
                                            "Likely implementation error or a breach of type safety\n\
                                             The type system is unsound by design\n\
                                             because the primitive `rec` fixpoint combinator is present"⟩

def Value.toStr : Value -> String
  | VI v | VB v => toString v | VU => toString ()
  | VS v => reprStr v
  | VEvalError s => s
  | VOpaque s   => s!"<${s}>"
  | VF _ _ _    => "<fun>"
  | VFRec _ _ _ => "<recfun?>"
  | VCtor n k acc =>
    s!"<{n}/{k}{acc.foldl (fun a s => a ++ " " ++ paren (constr? s || prod? s) (toStr s)) ""}>"
  | VConstr n fs => fs.foldl (fun a s => a ++ " " ++ paren (constr? s || prod? s) (toStr s)) n
  | VP v₁ v₂    => paren (prod? v₁) (toStr v₁) ++ "," ++ toStr v₂
    where
    paren b s := bif b then s!"({s})" else s
    prod? | VP _ _ => true | _ => false
    constr? | VConstr _ f => if f.isEmpty then false else true | _ => false
instance : ToString Value := ⟨Value.toStr⟩

open Logging (cyan blue error) in open Std.Format in
def Value.renderFmt : Value -> Std.Format
  | VI v | VB v => cyan $ toString v | VU => cyan $ toString ()
  | VS v => cyan $ reprStr v
  | VEvalError s => error s
  | VOpaque s => s!"<${s}>"
  | VF .. | VFRec .. => "<fun>"
  | VCtor n k acc =>
    letI acc := text s!"{blue n}/{cyan $ toString k}" :: acc.foldr (fun s a => (parenthesize s (renderFmt s)) :: a) []
    group ∘ nestD $ joinSep acc line
  | VConstr n fs =>
    group ∘ nestD $ joinSep (text (blue n) :: fs.foldr (fun s a => (parenthesize s (renderFmt s)) :: a) []) line
  | VP v₁ v₂ =>
    nestD ∘ group $ paren? (prod? v₁) (renderFmt v₁) ++ "," <+> renderFmt v₂
    where
    paren? b s := bif b then paren s else s
    prod? | VP _ _ => true | _ => false
    constr? | VConstr _ f => if f.isEmpty then false else true | _ => false
    parenthesize s :=
      paren? (constr? s || prod? s)
instance : Std.ToFormat Value := ⟨Value.renderFmt⟩

def Value.asType : Value -> Type
  | VI _ => Int | VB _ => Bool | VS _ => String
  | VP v₁ v₂ => asType v₁ × asType v₂
  | _ => Unit

@[never_extract, extern "lean_panic_fn"]
def panicD (m : String) (d : α) : α := d

def Value.get! : (v : Value) -> v.asType
  | VI i => i | VB b => b | VS s => s | VU => ()
  | VP v₁ v₂ => (get! v₁, get! v₂)
-- panic on
  | v@(VF ..)     => panicD s!"can't extract value from {v}" ()
  | v@(VFRec ..)  => panicD s!"can't extract value from {v}" ()
  | v@(VOpaque ..)    => panicD s!"can't extract value from {v}" ()
  | v@(VConstr ..)  => panicD s!"can't extract value from {v}" ()
  | v@(VCtor ..)  => panicD s!"can't extract value from {v}" ()
  | v@(VEvalError ..) => panicD s!"can't extract value from {v}" ()
