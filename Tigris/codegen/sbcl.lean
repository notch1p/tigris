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
- `clos[0]`:
  - mark as function-valued if clos is constructed from 𝐂.
- ite/switch to if/cond
- pairs to cons/car/cdr.
- ctors to `(cons tag (vector ...))`; proj w/ `(svref (cdr x) i)`
- isCtor to `(eq (car x) tag)` (arity check via simple-vector length later maybe?)
-/

namespace Codegen.CL open CPS

/-- `Shape` is now provided by the CPS IR. -/
abbrev ShapeEnv := Std.HashMap Name CPS.Shape
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
def withShapes (n : Name) (s : Shape) (k : S String) : S String :=
  get <&> fun ctx@{shapes,..} =>
    k.run' {ctx with shapes := shapes.insert n s}

attribute [inline] withIndent ind qsym funDesig withKnownFuns withShapes

def emitConst : IR.Const -> String
  | .unit     => "nil"
  | .int i    => toString i
  | .bool true  => "t"
  | .bool false => "nil"
  | .str s    => reprStr s

/-- NOTE: [EQUALITY](https://stackoverflow.com/a/548774)

| To compare against.. | Use..                                        |
|----------------------|----------------------------------------------|
| Objects/Structs      | `EQ`                                         |
| Symbols              | `EQ`                                         |
| NIL                  | `EQ`/`NULL`                                  |
| T                    | `EQ`                                         |
| Precise numbers      | `EQL`                                        |
| Floats               | `=`                                          |
| Char                 | `EQL`/`CHAR=`                                |
| List/Cons/Seq        | `EQUAL`                                      |
| String               | `EQUAL`/`EQUALP`/`STRING=` (symbols as well) |
| Tree                 | `TREE-EQUAL`                                 |

- performance: `eq` > `eql` > `equal` > `equalp`

- `%intOP` calls `sb-kernel:two-arg-OP`
  - `%int/` returns `0` when
    - divided by zero
    - otherwise calls `floor`
    - divisor should be a `fixnum`
- `%string=` calls `sb-kernel:%sp-string=`

-/
def emitPrim : IR.PrimOp -> String
  | .add => "%int+"
  | .sub => "%int-"
  | .mul => "%int*"
  | .div => "%int/"
  | .eqInt  => "%int="
  | .eqBool => "eq"
  | .eqStr  => "%string="

def isBoundVar : Name -> S Bool :=
  (get <&> (Std.HashMap.contains ∘ Ctx.shapes) <*> pure ·)
def setShape (x : Name) (s : CPS.Shape) : S Unit :=
  modify fun ctx => {ctx with shapes := ctx.shapes.insert x s}
def joinArgs (xs : Array Name) : String :=
  xs.foldl1D (· ++ " " ++ toString ·) ""
attribute [inline] isBoundVar setShape joinArgs

def asFuncValue (x : Name) : S String := do
  get <&> fun {shapes,knownFuns,..} =>
    match shapes.get? x with
    | some .fn => sym x
    | _ => if x ∈ knownFuns then funDesig x else sym x

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
      return s!"(cons {qsym t} (vector{fields.foldl (· ++ " " ++ ·) ""}))"
    else return s!"(cons {qsym t} (vector{fs.foldl (· ++ " " ++ sym ·) ""}))"

  | .isConstr s t _ => return s!"(eq (car {sym s}) {qsym t})"
  | .const k => return emitConst k
  | .alias y => return (sym y)

mutual
partial def emitLet1 (x : Name) (sh : CPS.Shape) (rhs : CRhs) (body : CExpr) : S String := do
  setShape x sh
  let rhsS <- emitCRhs rhs
  return s!"(let (({sym x} {rhsS}))\n\
              {<- ind}{<- withIndent (emitCExpr body)})"

partial def emitLetKont (kid param : Name) (kBody body : CExpr) : S String := do
  modify fun ctx => {ctx with localKont := ctx.localKont.insert kid}
  let ii <- ind
  return s!"(labels (({sym kid} ({sym param})\n\
                    {ii}{<- withIndent (emitCExpr kBody)}))\n\
              {ii}{<- withIndent (emitCExpr body)})"

partial def emitTail : CTail -> S String
  | .matchFail discr =>
    return s!"(error +NOMATCH+ :discr \"{discr}\")"
  | .appFun f p k =>
    get <&> fun {kontParam, knownFuns, shapes,..} =>
      let callee :=
        match shapes.get? f with
        | some .fn => s!"(the function {sym f})"
        | _ => if f ∈ knownFuns then funDesig f else s!"(the function {sym f})"
      let kArg := if k == kontParam then sym k else funDesig k
      s!"(funcall {callee} {sym p} {kArg})"
  | .appKont k v =>
    get <&> fun {localKont,..} =>
      if k ∈ localKont then s!"({sym k} {sym v})"
      else s!"(funcall (the function {sym k}) {sym v})"
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
    return s!"(cond\n{ii}{br}{dflt})"
  | .switchCtor s cases d? => do
    let ii <- ind
    let br <- cases.mapM fun (tag, ar, b) => do
      let b <- withIndent $ withIndent $ withShapes s (.ctor tag ar) $ (emitCExpr b)
      return s!"((eq (car {sym s}) {qsym tag})\n{ii}  {b})"
    let defs <- d?.mapM (withIndent $ withIndent $ emitCExpr ·)
    let br := br.foldl1D (· ++ "\n" ++ ii ++ ·) ""
    let dflt := defs.elim "" fun d => s!"\n{ii}(t\n{ii}  {d})"
    return s!"(cond\n{ii}{br}{dflt})"

partial def emitLetRec (funs : Array CFun) (body : CExpr) : S String :=
  withKnownFuns funs do
    let defs <- funs.mapM fun f => do
      modify fun ctx =>
        {ctx with localKont    := ∅
        ,         shapes       := Std.HashMap.insert ∅ f.payloadParam f.payloadShape
        ,         payloadParam := f.payloadParam
        ,         kontParam    := f.kontParam}
      let b <- withIndent (emitCExpr f.body)
      return s!"({sym f.fid} ({sym f.payloadParam} {sym f.kontParam})\n{b})"
    let defs := defs.foldl1D (· ++ "\n" ++ ·) ""
    return s!"(labels ({defs})\n{<- ind}{<- withIndent (emitCExpr body)})"

partial def emitCExpr : CPS.CExpr -> S String
  | .let1 x sh rhs b => emitLet1 x sh rhs b
  | .letKont k p kb b => emitLetKont k p kb b
  | .letRec funs b => emitLetRec funs b
  | .tail t => emitTail t
end

def emitFun (knownFuns : FunSet) (f : CFun) : String :=
  let body := withIndent (withIndent (emitCExpr f.body)) |>.run' $
    -- use payload shape
    let shapes := Std.HashMap.insert ∅ f.payloadParam f.payloadShape
    { payloadParam := f.payloadParam
    , kontParam    := f.kontParam
    , knownFuns
    , shapes}
  let pragma := s!"(declare (optimize (speed 3) (safety 0) (debug 0)) \
                            (ignorable {sym f.payloadParam}))"
  s!"(defun {sym f.fid} ({sym f.payloadParam} {sym f.kontParam})\n  {pragma}\n  {body})\n"

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
