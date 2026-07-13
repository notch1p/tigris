import Tigris.TCNF.nf

/-!
# A new SBCL backend based on TCNF

## Notable Encodings.

- Closures and Calling.
  A CL struct carrying the function and its arity.
  - Captured env is held by a native lambda (fixed by the caller).
  - Known partial application is also fixed by a native lambda
  - direct (or KOC'd) calls stay flat;
  - generic calls go through arity-specialized gapply<n> (emitted on demand)
  with %apply-slow (subsumes curryN) for actual arity mismatch cases.

  We distinguish gapply with %apple-slow because it is more than likely
  generic calls are arity matched instead of the other way; And %apply-slow is
  really _slow_: apply/length/append/subseq/nthcdr/&rest -- SBCL's funcall is
  just performant as a native call, thus we maximizing on that.
  See also
  1. https://cmucl.org/docs/cmu-user/cmu-user.html#Function-Call-1
  2. Tigris.TCNF.

- Variants.
  Also a CL struct. We emit a abstract parent that carries an integer tag,
  and one child defstruct per ctor that overrides the tag default;
  branch dispatch becomes a case jump table on the tag,
  field projections become a slot read, which, is also optimized by SBCL.

- Jump points.
  Since jump points take arguments, a more primitive approach of tagbody/go
  (or block/return-from) would require more works to be done. Since jps aren't
  recursive for now, we use labels directly.

- Runtime.
  Reusing the old runtime.lisp as it is rather self-contained.

- Type hints.
  Planned.
  Using declare/declaim/the to annotate variables, enabling further optimizations
  from SBCL's end.
-/

namespace TCNF.CL open Std

inductive Sexp where
  | int  (i : Int)
  | str  (s : String)
  | sym  (s : String)
  | list (xs : Array Sexp)
deriving Inhabited

structure Ctx where
  names     : HashMap FVarId String
  declArity : HashMap FVarId Nat
  ctorInfo  : HashMap String (String × Nat × Nat)   -- ctor ↦ (tycon, tagIdx, #fields)
  tys       : HashSet String                        -- user data/class type names (parent structs)

structure Mut where
  genArities : HashSet Nat := ∅
  gensym     : Nat := 0

structure CLModule where
  funs     : Array Sexp
  vals     : Array Sexp
  main     : Sexp
  tail     : Array Sexp
  declaims : Array Sexp

abbrev CGM := ReaderT Ctx (StateRefT Mut IO)

/-!
# Naming.

variables have the form `|<binderName>-<fvarId>|`.
Type/ctor names are namespaced under a `/`-prefix
-/

def isBuiltinTy (t : String) : Bool :=
  t == "Int" || t == "Bool" || t == "String" || t == "Unit" || t == "Empty"

def sanitize (s : String) : String :=
  s.foldl (fun a c =>
            a.push $
              match c with
              | '|'  => '-'
              | '\\' => '-'
              | c    => c)
          ""
def parentSym  (tycon : String)       : String := s!"|{tycon}|"
def tagAcc     (tycon : String)       : String := s!"|{tycon}/tag|"
def ctorStruct (c : String)           : String := s!"|c/{c}|"
def mkSym      (c : String)           : String := s!"|mk/{c}|"
def predSym    (c : String)           : String := s!"|{c}?|"
def fieldAcc   (c : String) (i : Nat) : String := s!"|{c}/f{i}|"

def primFn : PrimOp -> String
  | .add => "%int+" | .sub => "%int-" | .mul => "%int*" | .div => "%int/"
  | .eqInt => "%int=" | .eqStr => "%string=" | .eqBool => "eq"

/--
`clType` maps an ML type to a CL type specifier for declaim/declare/slot
`:type`, or `none` when no monotype exists. Polymorphic positions is T.
`tys` is the set of user data/class type
names, whose values are the corresponding parent defstruct.
-/
def clType (tys : HashSet String) : MLType -> Option String
  | .TSch (.Forall _ _ t) => clType tys t
  | .TCon "Int"           => some "integer"
  | .TCon "Bool"          => some "boolean"
  | .TCon "String"        => some "string"
  | .TCon "Unit"          => some "null"
  | .TProd ..             => some "cons"
  | .TArr ..              => some "clos"                           -- `clos` CL type
  | .TApp (.TCon c) _
  | .TCon c =>
    if tys.contains c then some (parentSym c) else none            -- inductive types
  | _                           => none

/-- A CL value of `clType` `t` valid as a `defstruct` slot default.
Restricts typed slots to scalars whose `nil`/zero default type-checks at macroexpansion-time
Note that boa constructors always supply the slot,
so the default is otherwise unused. -/
def slotDefault? : String -> Option Sexp
  | "integer"          => some (.int 0)
  | "boolean" | "null" => some (.sym "nil")
  | "string"           => some (.str "")
  | _                  => none

/-- Filters out builtin/empty/newtypes. see also TyDecl.isNewtype. -/
def structTyNames (tyDecl : TyMap) : HashSet String :=
  tyDecl.fold (init := ∅) fun acc tycon td =>
    if isBuiltinTy tycon || td.ctors.isEmpty || td.isNewtype
    then acc else acc.insert tycon

def freshG : CGM String :=
  modifyGet fun s => (s!"|g{s.gensym}|", {s with gensym := s.gensym + 1})
def noteArity (n : Nat) : CGM Unit :=
  modify fun s => {s with genArities := s.genArities.insert n}
def declArity? (id : FVarId) : CGM (Option Nat) := read <&> (·.declArity[id]?)
def ctorInfo?  (c : String)  : CGM (Option (String × Nat × Nat)) := read <&> (·.ctorInfo[c]?)
def valSym (id : FVarId) : CGM String :=
  read <&> fun {names,..} =>
    match names[id]? with
    | some nm => s!"|{sanitize nm}-{id}|"
    | none    => s!"|v-{id}|"
attribute [inline]
  sanitize parentSym tagAcc ctorStruct
  mkSym predSym fieldAcc freshG
  noteArity declArity? ctorInfo?

/-! CL-idiomatic layout. Since `Std.Format` alignment is margin-relative (not
column-relative), continuation lines align only for forms that begin at the
margin — which is exactly the case for line-broken bodies, so this dispatches on
the head symbol into the standard indentation classes. -/
namespace PP open Std.Format
def joinSuffix' [Std.ToFormat α] (xs : Subarray α) (suffix : Format) :=
  xs.foldl (· ++ suffix ++ format ·) .nil

def paren' f := group $ text "(" ++ f ++ text ")" -- non-nesting version of paren

def joinSep'' [Std.ToFormat α] (arr : Subarray α) (sep : Format) : Format :=
  if h : arr.size = 0 then nil
  else arr.drop 1 |>.foldl (· ++ sep ++ format ·) (format arr[0])

def callForm (op : String) (args : Subarray Format) : Format :=
  if args.isEmpty then paren op
  else paren $ op <+> nest (op.length + 2) (joinSep'' args line)

def blockForm (op : String) (dist body : Subarray Format) : Format :=
  let hdr := dist.foldl (fun a d => a ++ text " " ++ d) (text op)
  paren' $ hdr ++ nestD (joinSuffix' body "\n")

def itemsForm (fs : Subarray Format) : Format :=
  paren $ nest 1 (joinSep'' fs "\n")

def letForm (op : String) (bindings : Format) (body : Subarray Format) : Format :=
  paren $ (op <> nest op.length bindings) ++ nestD (joinSuffix' body line)

def fmtSexp : Sexp -> Format
  | .int i => text (toString i)
  | .str s => repr s
  | .sym s => text s
  | .list xs =>
    let fmts := xs.attach.map (fun ⟨a, h⟩ => fmtSexp a) |>.toSubarray
    if h : 0 < xs.size then
      match xs[0] with
      | .sym op =>
        let rest := fmts[1:]
        match op with
        | "defun" | "defmacro" | "defmethod" => blockForm op rest[0:2] rest[2:]
        | "lambda" | "defparameter" | "defvar" | "defstruct"
        | "when"   | "unless"       | "if"
        | "case"   | "ecase"        | "typecase" | "etypecase"
        | "dolist" | "dotimes"      => blockForm op rest[0:1] rest[1:]
        | "let" | "let*" | "flet" | "labels" => letForm op (rest[0]?.getD (text "()")) rest[1:]
        | "cond" | "progn" | "and" | "or"    => blockForm op #[].toSubarray rest
        | _ => callForm op rest
      | _ => itemsForm fmts
    else text "()"
termination_by e => e

instance : ToFormat Sexp := ⟨fmtSexp⟩
end PP

end TCNF.CL
