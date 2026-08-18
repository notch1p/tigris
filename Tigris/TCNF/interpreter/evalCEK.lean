import Tigris.TCNF.interpreter.types
import Tigris.TCNF.entrypoint
namespace TCNF.Interpreter open Std TCNF open MLType (TypingError) open Array (seq2fold2)

private def checkInterrupt : EIO TypingError Unit :=
  IO.checkCanceled >>= fun
  | true => throw .Interrupted
  | false => return ()
local macro "withInterrupt!" x:doSeq : term => ``(do $x)

protected def normalizeSch : Scheme -> Scheme := Prod.fst ∘ SysF.renameMVSch

def computeLet (lv : LetValue .postCC) : EvaluatorCEK Value :=
  match lv with
  | .lit k         => return asConst k
  | .pair p q      => .pair <$> evalAtom p <*> evalAtom q
  | .proj i x      => projPair x i =<< lookup x
  | .field _ i x   => projConstr x i =<< lookup x
  | .ctor t as     => .constr t <$> as.mapM evalAtom
  | .prim op args  => evalPrimBinop op =<< args.mapM evalAtom
  | .extern f args => evalExtern f =<< args.mapM evalAtom
  | .isCtor x t a =>
    lookup x <&> fun
    | .constr t' as => .bool (t' == t && as.size == a)
    | _             => .bool false
  | .mkClos c env => .clos c <$> env.mapM evalAtom
  | _ => impossibleF! "computeLet: unexpected {format lv |>.pretty (indent := 23) (column := 23)}"

mutual
/-- evaluate the kontinuation stack. -/
partial def «continue» (v : Value) (kont : Kont) : EvaluatorCEK Value := fun s =>
  match kont with
  | .halt => return v
  | .letK fv rest env k =>
    loop rest k {s with locals := env.insert fv v}
  | .appK _ captured remaining k =>
    match v with
    | .clos c cap => applyCEK c (captured ++ cap) remaining k s
    | _ => impossibleT! "over-application produced non-function {v}" kont $ s

partial def applyCEK
  (codeptr : FVarId)
  (captured : Array Value)
  (args : Subarray Value)
  (kont : Kont) : EvaluatorCEK Value := fun s@{locals, globaldecls,..} =>
  withInterrupt!
    let some {params,body,..} := globaldecls[codeptr]? | impossibleT! "undefined function #{codeptr}" kont $ s
    let arity  := params.size - captured.size
    let ass    := args.size
    if arity == ass then
      let locals := seq2fold2 (fun acc a b => acc.insert b.fvarId a) locals captured args params
      loop body kont {s with locals}
    else if arity > ass then «continue» (.clos codeptr (captured ++ args)) kont s
    else
      let locals := seq2fold2 (fun acc a b => acc.insert b.fvarId a) locals captured args[:arity] params
      loop body (.appK codeptr #[] args[arity:] kont) {s with locals}

partial def evaluateLet (lv : LetValue .postCC) (kont : Kont) : EvaluatorCEK Value :=
  match lv with
  | .app 0 as | .pap 0 as =>
    impossibleT! "All branches failed to match against {format as}" kont
  | .app f as | .pap f as => withInterrupt!
    let fv <- lookup f
    let args <- as.mapM evalAtom
    match fv with
    | .clos c cap => applyCEK c cap args.toSubarray kont
    | v => impossibleT! "callee {v} is not a code pointer" kont
  | _ => do
    let v <- computeLet lv
    «continue» v kont

partial def loop (code : Code .postCC) (kont : Kont) : EvaluatorCEK Value := fun s@{locals, joins,..} => withInterrupt!
  match code with
  | .let {fvarId, value,..} b =>
    -- same tail-call peephole as in CL backend. here we skip the letK frame
    let tail? := match b with
      | .ret (.fvar r) => r == fvarId
      | _              => false
    let kont' := if tail? then kont else .letK fvarId b locals kont
    evaluateLet value kont' s
  | .ret a =>
    let v <- evalAtom a s
    «continue» v kont s
  | .cases d _ alts =>
    let v <- lookup d s
    match v with
    | .unit =>
      match alts.find? fun | .default _ | .const .PUnit _ => true | _ => false
      with | some (.default k) | some (.const _ k) => loop k kont s
           | _ => impossibleT! "Can't match against {d} => ()" kont $ s
    | .int i =>
      match alts.find? fun | .default _ => true | .const (.PInt i') _ => i == i' | _ => false
      with | some (.default k) | some (.const _ k) => loop k kont s
           | _ => impossibleT! "Can't match against {d} => {i}" kont $ s
    | .bool b =>
      match alts.find? fun | .default _ => true | .const (.PBool b') _ => b == b' | _ => false
      with | some (.default k) | some (.const _ k) => loop k kont s
           | _ => impossibleT! "Can't match against {d} => {b}" kont $ s
    | .str str =>
      match alts.find? fun | .default _ => true | .const (.PStr s') _ => str == s' | _ => false
      with | some (.default k) | some (.const _ k) => loop k kont s
           | _ => impossibleT! "Can't match against {d} => {repr str}" kont $ s
    | .constr t as =>
      match alts.find? fun | .default _ => true | .ctor t' .. => t' == t | _ => false with
      | some (.default k) => loop k kont s
      | some (.ctor _ ps k) =>
        let locals := Array.foldl2 (fun acc a {fvarId,..} => acc.insert fvarId a) locals as ps
        loop k kont {s with locals}
      | _ => impossibleT! "Can't match against {d} => {t}" kont $ s
    | v => impossibleT! "Discriminant {v} is neither variant nor constant" kont $ s
  | .jp {fvarId, params, body,..} k =>
    let ps := params.map Param.fvarId
    loop k kont {s with joins := joins.insert fvarId (ps, body, locals)}
  | .jmp jp args => do
    let some (ps, body, capturedEnv) := s.joins[jp]? | impossibleT! "undefined join point #{jp}" kont $ s
    let as <- args.mapM evalAtom s
    let locals := Array.foldl2 (fun acc fv a => acc.insert fv a) capturedEnv ps as
    loop body kont {s with locals}
  | .unreach _ => impossibleT! "unreachable code has been reached" kont $ s
end
open Format (fill group pretty nestD)
def check (s : String) (print? := true) : LowerM Value := do
  let (_, topdecl) <- Parsing.parseModuleIR s initState
  let stage₀@(_, E, _) <- inferToplevelC topdecl MLType.defaultE' |>.mapError toString |> EIO.ofExcept
  let (fdecls, _, ctors) <- inferToplevelF stage₀ |>.mapError toString |> EIO.ofExcept
  let {decls, main} <- lowerModuleCCOpt fdecls ctors E.tyDecl
  let mut globaldecls := ∅
  let mut topvals := ∅
  let mut lastVal := Value.unit
  for d@{fvarId, arity, body, name,..} in decls.push main do
    if arity > 0 then
      if let some ty := E.E[name]? then
        if print? then liftEIO $ println! template name "<fun>" $ Interpreter.normalizeSch ty
      globaldecls := globaldecls.insert fvarId d
      topvals := topvals.insert fvarId (.clos fvarId #[])
    else
      let st : IState := {globaldecls, topvals, locals := ∅, joins := ∅}
      let v <- loop body .halt |>.run st |>.adapt toString
      if let some ty := E.E[name]? then
        if print? then liftEIO $ println! template name v $ Interpreter.normalizeSch ty
      topvals := topvals.insert fvarId v
      lastVal := v
  return lastVal

def checkFile (s : System.FilePath) (print? := true) : IO Value := do
  let s <- IO.FS.readFile s
  EIO.toIO .userError $ check s print?

def main (args : List String) := args.forA fun p => () <$ checkFile p
