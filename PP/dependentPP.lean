import PP.ffidecl

namespace PrettyPrint

namespace Text

@[inline] def bold s t := bif t then s!"\x1b[1m" ++ s ++ "\x1b[0m" else s

end Text

abbrev ToProd (as : List α) (motive : Type -> Type) : Type :=
  match as with
  | [] => PUnit
  | [_] => motive α
  | _ :: x :: xs =>
    motive α × ToProd (x :: xs) motive

def toProd (l : List α) : ToProd l id :=
  match l with
  | [] => ()
  | [x] => (x)
  | x :: y :: ys => (x, toProd $ y :: ys)

inductive Alignment | left | center | right
inductive PadsBy
  /-- pads according to the largest cell -/
  | perCell
  /-- pads according to the largest cell _per column_ -/
  | perCol

abbrev Row (header : List String) := ToProd header id
abbrev Align (header : List String) := ToProd header λ _ => Alignment
abbrev TableOf (header : List String) := Array $ Row header
abbrev OverrideWidth (header : List String) := ToProd header λ _ => Option Nat

def ovTostr (ov : OverrideWidth header) : String :=
  match header with
  | [] => "" | [_] => toString ov
  | %[_, _ | _] => toString ov.1 ++ ovTostr ov.2

def rowLengthToList (t : Row header) : OverrideWidth header :=
  match header with
  | [] => () | [_] => some t.length
  | %[_, _ | _] => (some $ t.1.length, rowLengthToList (t.2))

def zeroOverride (header : List String) : OverrideWidth header :=
  match header with
  | [] => () | [_] => none
  | %[_, y | ys] => (none, zeroOverride (y :: ys))

def maxN (h₁ h₂ : OverrideWidth header) : OverrideWidth header :=
  match header with
  | [] => () | [_] => max h₁ h₂
  | %[_, _ | _] => (max h₁.1 h₂.1, maxN h₁.2 h₂.2)

/--
  h₂ overrides h₁.
-/
def merge (h₁ h₂ : OverrideWidth header) : OverrideWidth header :=
  match header with
  | [] => () | [_] => max h₁ h₂
  | %[_, _ | _] => (h₂.1 <|> h₁.1, merge h₁.2 h₂.2)

instance : ToString $ OverrideWidth header := ⟨ovTostr⟩
instance : Union    $ OverrideWidth header := ⟨merge⟩
instance : Max      $ OverrideWidth header := ⟨maxN⟩
instance : Zero     $ OverrideWidth header := ⟨zeroOverride header⟩

structure PPSpec (header : List String) where
  align   : Align header
  width   : OverrideWidth header := 0
  header? : Bool := true
  margin  : Nat := 3
  padsBy  : PadsBy := .perCol
  bold?   : Bool := true

def calcMaxWidthPerCol (t : TableOf header) : OverrideWidth header :=
  match h : header with
  | [] => ()
  | [_] => 
    some $ t.push (h ▸ toProd header) |>.foldl (flip $ max ∘ String.length) 0
  | %[_, _ | _] => 
    t.push (h ▸ toProd header) |>.foldl (flip $ flip (h ▸ max) ∘ rowLengthToList) $ h ▸ 0

def calcMaxWidthRow (t : Row header) : Nat :=
  match header with
  | [] => 0 | [_] => String.length t
  | %[_, _ | _] => max (String.length t.1) (calcMaxWidthRow t.2)

def pad n (c := ' ') := c.repeat n

open Alignment Text in
def withAlign (acc term : String) padding margin b?
  | left   => s!"{acc}{pad margin}{bold term b?}{pad padding}"
  | right  => s!"{acc}{pad margin}{pad padding}{bold term b?}"
  | center => let hp := if 1 &&& padding == 0
                        then padding >>> 1 else (padding + 1) >>> 1
              let mg := if 1 &&& margin == 0
                        then margin >>> 1 else (margin + 1) >>> 1
              s!"{acc}{pad hp}{pad mg}{bold term b?}{pad mg}{pad hp}"

def padRow (mw : Nat) (spec : PPSpec header) (t : Row header) (acc := "")
  : String :=
  let {align := as, width := ov,margin := mg,..} := spec
  match header with
  | [] => ""
  | [_] => if let some w := ov then withAlign acc t (w - t.length) mg false as
           else withAlign acc t (mw - t.length) mg false as
  | _ :: _ :: _ =>
    match ov with
    | (some w, ovs) =>
        padRow mw {spec with align := as.2, width := ovs} t.2
      $ withAlign acc t.1 (w - t.1.length) mg false as.1
    | (_, ovs) =>
        padRow mw {spec with align := as.2, width := ovs} t.2
      $ withAlign acc t.1 (mw - t.1.length) mg false as.1

def padHeader (mw : Nat) (spec : PPSpec header) (accl := 0) (acc := "")
  : String × Nat :=
  let {align := as, width := ov,margin := mg, bold?,..} := spec
  match header with
  | [] => ("", 0)
  | [x] => if let some w := ov
           then (withAlign acc x (w - x.length) mg bold? as, mg + w + accl)
           else (withAlign acc x (mw - x.length) mg bold? as, mg + accl)
  | x :: _ :: _ =>
    match ov with
    | (some w, ovs) =>
        padHeader mw {spec with align := as.2, width := ovs} (accl + w + mg)
      $ withAlign acc x (w - x.length) mg bold? as.1
    | (_, ovs) =>
        padHeader mw {spec with align := as.2, width := ovs} (accl + mw + mg)
      $ withAlign acc x (mw - x.length) mg bold? as.1

def calcMaxWidthTbl (t : TableOf header) : Nat :=
  t.foldl (init := 0) fun a s => max a $ calcMaxWidthRow s

def tabulate (name : String) (spec : PPSpec header) (t : TableOf header) : String :=
  let mw := calcMaxWidthTbl t
  let spec :=
    if spec.padsBy matches .perCell
    then spec else {spec with width := calcMaxWidthPerCol t ∪ spec.width}
  let bd := t.foldr (init := "") (padRow mw spec · ++ "\n" ++ ·)
  if spec.header? then
    let (hd, totl) := padHeader mw spec
    s!"{withAlign "" name 0 0 true .left}\n{hd}\n{pad totl '='}\n{bd}"
  else bd

end PrettyPrint
