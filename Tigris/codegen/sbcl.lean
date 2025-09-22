import Tigris.cps.cps

/-!
Simple codegen from CPS IR to SBCL (w/ labels + funcall).
- continuations are created as-is, no defunctionalization is going on.

- `(defun fid (payload k))` for toplevel functions
- let1 to `let`
- CRhs to +, -, *, /, car/cdr, svref, constructors.
- `letKont k v = ...` to `(labels ((k (v) ...)) body)`
- `APPLY k v` to
  - `k v` where `k` is local
  - `(funcall k v)` where `k` is at parameter position
- `𝐂⟦codePtr, env⟧`:
  - #'codePtr if codePtr is toplevel/label-bound
  - otherwise store as-is
- `𝐄⟦field,*⟧`, for each field `f`,
  - store as-is if `f` is a local function-valued var
  - otherwise if `f` is toplevel/label-bound, store `#'f`
  - otherwise, store as-is.
- `f(a, k)`:
  - `(funcall f ...)` where f is local variable
  - `(funcall #'f ...)` where f is toplevel/label-bound
- `clos[0]`:
  - mark as function-valued if clos is constructed from 𝐂.
- ite/switch to if/cond
- pairs to cons/car/cdr.
- ctors to `(cons tag (vector ...))`; proj w/ `(svref (cdr x) i)`
- isCtor to `(eq (car x) tag)` (arity check via simple-vector length later maybe?)
-/

namespace Codegen.CL open CPS

inductive Shape where
  | unknown
  | pair
  | ctor (tag : Name) (arity : Nat)
  | fn -- function object inside value cell
deriving Inhabited, BEq, Repr

abbrev ShapeEnv := Std.HashMap Name Shape
abbrev KontSet := Std.HashSet Name
abbrev FunSet  := Std.HashSet Name

structure Ctx where
  shapes       : ShapeEnv := {}
  localKont    : KontSet  := {}
  knownFuns    : FunSet   := {}
  payloadParam : Name := "payload"
  kontParam    : Name := "k"
  indent       : Nat := 0
deriving Inhabited

abbrev S := StateM Ctx

def withIndent (k : S String) : S String :=
  get <&> fun ctx@{indent,..} =>
    k.run' {ctx with indent := indent + 2}
def ind : S String := (' '.repeat ∘ Ctx.indent) <$> get
def sym (s : Name) : String :=
  letI esc := s.foldl (init := "|") fun acc ch =>
    match ch with
    | '|' => acc ++ "\\|"
    | '\\' => acc ++ "\\\\"
    | _ => acc.push ch
  esc.push '|'
def qsym (t : Name) : String := s!"'{sym t}"
def funDesig (f : Name) : String := "#'" ++ sym f
def withKnownFuns (extra : Array CFun) (k : S String) : S String :=
  get <&> fun ctx@{knownFuns,..} =>
    k.run' {ctx with knownFuns := extra.foldl (·.insert ·.fid) knownFuns}

attribute [inline] withIndent ind qsym funDesig

def emitConst : IR.Const -> String
  | .unit     => "nil"
  | .int i    => toString i
  | .bool true  => "t"
  | .bool false => "nil"
  | .str s    => reprStr s

def emitPrim : IR.PrimOp -> String
  | .add => "+"
  | .sub => "-"
  | .mul => "*"
  | .div => "/"
  | .eqInt  => "="
  | .eqBool => "eql"
  | .eqStr  => "string="

def isBoundVar : Name -> S Bool :=
  (get <&> (Std.HashMap.contains ∘ Ctx.shapes) <*> pure ·)
def setShape (x : Name) (s : Shape) : S Unit :=
  modify fun ctx => {ctx with shapes := ctx.shapes.insert x s}
def joinArgs (xs : Array Name) : String :=
  xs.foldl1D (· ++ " " ++ toString ·) ""
attribute [inline] isBoundVar setShape joinArgs

def recordShape (x : Name) : CRhs -> S Unit
  | .mkPair _ _    => setShape x .pair
  | .mkConstr t fs => setShape x (.ctor t fs.size)
  | .alias y       =>
    modify fun ctx =>
      let sh := ctx.shapes.getD y .unknown
      {ctx with shapes := ctx.shapes.insert x sh}
  | .proj s i      =>
    modify fun ctx@{shapes, payloadParam,..} =>
      if s == payloadParam then
        if i == 0 then {ctx with shapes := shapes.insert x .pair}
        else {ctx with shapes := shapes.insert x .unknown}
      else
        match shapes.getD s .unknown with
        | .ctor "𝐂" _ =>
          if i == 0 then {ctx with shapes := shapes.insert x .fn}
          else {ctx with shapes := shapes.insert x .unknown}
        | _ => {ctx with shapes := shapes.insert x .unknown}
  | _ => setShape x .unknown

def asFuncValue (x : Name) : S String := do
  get <&> fun {shapes,knownFuns,..} =>
    match shapes.get? x with
    | some .fn => sym x
    | _ =>
      if x ∈ knownFuns then funDesig x else sym x

def emitCRhs : CRhs -> S String
  | .prim op args =>
    let fn := emitPrim op
    let as := joinArgs $ args.map sym
    return s!"({fn} {as})"
  | .proj s i =>
    get <&> fun {shapes,..} =>
      match shapes.getD s .unknown with
      | .pair =>
        if i == 0 then s!"(car {sym s})"
        else if i == 1 then s!"(cdr {sym s})"
        else s!"(error \"invalid projection: {sym s}[{i}]\")"
      | _ => s!"(svref (cdr {sym s}) {i})"
  | .mkPair a b => return s!"(cons {sym a} {sym b})"
  | .mkConstr t fs => do
    if h : t == "𝐂" ∧ fs.size = 2 then
      let (code, env) := (fs[0], fs[1])
      let codeField <- asFuncValue code
      return s!"(cons {qsym t} (vector {codeField} {sym env}))"
    else if t == "𝐄" then
      let fields <- fs.mapM asFuncValue
      return s!"(cons {qsym t} (vector {joinArgs fields}))"
    else return s!"(cons {qsym t} (vector {joinArgs $ fs.map sym}))"

  | .isConstr s t _ => return s!"(eq (car {sym s}) {qsym t})"
  | .const k => return emitConst k
  | .alias y => return (sym y)

mutual
partial def emitLet1 (x : Name) (rhs : CRhs) (body : CExpr) : S String := do
  let rhsS <- emitCRhs rhs
  recordShape x rhs -- emit first then update, important for recursive functions
  return s!"(let (({sym x} {rhsS}))\n\
              {<- ind}{<- withIndent (emitCExpr body)})"

partial def emitLetKont (kid param : Name) (kBody body : CExpr) : S String := do
  modify fun ctx => {ctx with localKont := ctx.localKont.insert kid}
  let ii <- ind
  return s!"(labels (({sym kid} ({sym param})\n\
                    {ii}{<- withIndent (emitCExpr kBody)}))\n\
              {ii}{<- withIndent (emitCExpr body)})"

partial def emitTail : CTail -> S String
  | .appFun f p k =>
    get <&> fun {kontParam, knownFuns, shapes,..} =>
      let callee :=
        match shapes.get? f with
        | some .fn => sym f
        | _ => if f ∈ knownFuns then funDesig f else sym f
      let kArg := if k == kontParam then sym k else funDesig k
      s!"(funcall {callee} {sym p} {kArg})"
  | .appKont k v =>
    get <&> fun {localKont,..} =>
      if k ∈ localKont then s!"({sym k} {sym v})"
      else s!"(funcall {sym k} {sym v})"
  | .halt v => return s!"(progn {sym v})"
  | .ite c t e => do
    let ii <- ind
    let t <- withIndent (emitCExpr t)
    let e <- withIndent (emitCExpr e)
    return s!"(if {sym c}\n{ii}{t}\n{ii}{e})"
  | .switchConst s cases d? => do
    let ii <- ind
    let br <- cases.mapM fun (k, b) => do
      let b <- withIndent $ withIndent (emitCExpr b)
      pure s!"((equal {sym s} {emitConst k})\n{ii}  {b})"
    let defs <- d?.mapM (withIndent $ withIndent $ emitCExpr ·)
    let br := br.foldl1D (· ++ "\n" ++ ii ++ ·) ""
    let dflt := defs.elim "" fun d => s!"\n{ii}(t\n{ii}  {d})"
    return s!"(cond\n{ii}{br}{ii}{dflt})"
  | .switchCtor s cases d? => do
    let ii <- ind
    let br <- cases.mapM fun (tag, _, b) => do
      let b <- withIndent $ withIndent (emitCExpr b)
      return s!"((eq (car {sym s}) {qsym tag})\n{ii}  {b})"
    let defs <- d?.mapM (withIndent $ withIndent $ emitCExpr ·)
    let br := br.foldl1D (· ++ "\n" ++ ii ++ ·) ""
    let dflt := defs.elim "" fun d => s!"\n{ii}(t\n{ii}  {d})"
    return s!"(cond\n{ii}{br}{dflt})"

partial def emitLetRec (funs : Array CFun) (body : CExpr) : S String :=
  withKnownFuns funs do
    let defs <- funs.mapM fun {payloadParam, kontParam, body, fid} => do
      modify fun ctx =>
        {ctx with localKont := ∅
        ,         shapes    := Std.HashMap.insert ∅ payloadParam .pair
        ,         payloadParam
        ,         kontParam}
      let b <- withIndent (emitCExpr body)
      return s!"({sym fid} ({sym payloadParam} {sym kontParam})\n{b})"
    let defs := defs.foldl1D (· ++ "\n" ++ ·) ""
    return s!"(labels ({defs})\n{<- ind}{<- withIndent (emitCExpr body)})"

partial def emitCExpr : CPS.CExpr -> S String
  | .let1 x rhs b => emitLet1 x rhs b
  | .letKont k p kb b => emitLetKont k p kb b
  | .letRec funs b => emitLetRec funs b
  | .tail t => emitTail t
end

def emitFun (knownFuns : FunSet) : CFun -> String
  | {body, payloadParam, kontParam, fid} =>
    let body := withIndent (withIndent (emitCExpr body)) |>.run' $
      let shapes := Std.HashMap.insert ∅ payloadParam Shape.pair
      { payloadParam
      , kontParam
      , knownFuns
      , shapes}
    let pragma := "(declare (optimize (speed 3) (safety 0) (debug 0)))"
    s!"(defun {sym fid} ({sym payloadParam} {sym kontParam})\n  {pragma}\n  {body})\n"

def emitModule (m : CModule)
  (package : Option String := none) (addDriver := true)
  : (String × String × String × String) :=
  let allFuns := m.funs.foldl (·.insert ·.fid) (.insert ∅ m.main.fid)
  let hd := package.elim "" fun p => s!"(in-package {p})\n\n"
  let funs := m.funs.foldl (· ++ "\n" ++ emitFun allFuns ·) ""
  let main := emitFun allFuns m.main
  let driver :=
    if addDriver then
      let start := "__start"
      s!"(defun {sym start} ()\n  \
            (format t \"~A\"\n    \
              (funcall {funDesig m.main.fid} nil #'identity)))\n"
    else ""
  (hd, funs, main, driver)

end Codegen.CL
