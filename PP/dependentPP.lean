import PP.ffidecl

namespace PrettyPrint

namespace Text

inductive Color | black | red | green | yellow | blue | magenta | cyan | white | defaultColor
inductive Style | bold  | dim | italic | underline | blinking | inverse | hidden | strikethrough
open Color Style

def styleN
  | bold     => "1" | dim     => "2" | italic => "3" | underline     => "4"
  | blinking => "5" | inverse => "7" | hidden => "8" | strikethrough => "9"

def fgN
  | black   => "30" | red     => "31" | green => "32" | yellow => "33"
  | blue    => "34" | magenta => "35" | cyan  => "36" | white  => "37"
  | defaultColor => "39"

def bgN
  | black => "40" | red     => "41" | green => "42" | yellow => "43"
  | blue  => "44" | magenta => "45" | cyan  => "46" | white  => "47"
  | defaultColor => "49"

def ESC   := "\x1b["
def RESET := "\x1b[0m"

structure TStyle where
  style : List Style := []
  fg : Color := defaultColor
  bg : Color := defaultColor
instance : EmptyCollection TStyle := ⟨{}⟩
@[inline] def TStyle.buildPrefix : TStyle -> String
  | {style, fg, bg} =>
     ESC
  ++ fgN fg
  ++ ";" ++ bgN bg
  ++ style.foldl (· ++ ";" ++ styleN ·) ""
  ++ "m"

structure SString where
  s : String
  style : TStyle
instance : ToString SString := ⟨(·.s)⟩

namespace SString
def str : String -> SString := fun s => ⟨s, ∅⟩
def byl str := SString.mk str {style := [.bold], fg := .yellow}
def blu str := SString.mk str {fg := .blue}
def length : SString -> Nat := fun {s,..} => s.length
def render : SString -> String
  | ⟨s, style⟩ => style.buildPrefix ++ s ++ RESET
end SString

@[inline] def mkBold s := SString.mk s {style := [.bold]} |>.render
@[inline] def mkBoldBlackWhite s :=
  SString.mk s {style := [.bold], fg := .black, bg := .white} |>.render

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
section
variable (header : List Text.SString)
abbrev Row := ToProd header id
abbrev Align := ToProd header λ _ => Alignment
abbrev TableOf := Array $ Row header
abbrev OverrideWidth := ToProd header λ _ => Option Nat

end

def ovTostr (ov : OverrideWidth header) : String :=
  match header with
  | [] => "" | [_] => toString ov
  | %[_, _ | _] => toString ov.1 ++ ovTostr ov.2

def rowLengthToList (t : Row header) : OverrideWidth header :=
  match header with
  | [] => () | [_] => some t.length
  | %[_, _ | _] => (some $ t.1.length, rowLengthToList (t.2))

def zeroOverride (header : List Text.SString) : OverrideWidth header :=
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

structure PPSpec (header : List Text.SString) where
  align   : Align header
  width   : OverrideWidth header := 0
  header? : Bool := true
  margin  : Nat := 3
  padsBy  : PadsBy := .perCol

def calcMaxWidthPerCol (t : TableOf header) : OverrideWidth header :=
  match h : header with
  | [] => ()
  | [_] =>
    some $ t.push (h ▸ toProd header) |>.foldl (flip $ max ∘ Text.SString.length) 0
  | %[_, _ | _] =>
    t.push (h ▸ toProd header) |>.foldl (flip $ flip (h ▸ max) ∘ rowLengthToList) $ h ▸ 0

def calcMaxWidthRow (t : Row header) : Nat :=
  match header with
  | [] => 0 | [_] => t.length
  | %[_, _ | _] => max t.1.length (calcMaxWidthRow t.2)

def pad n (c := ' ') := c.repeat n

open Alignment Text in
def withAlign (acc term : String) padding margin
  | left   => s!"{acc}{pad margin}{term}{pad padding}"
  | right  => s!"{acc}{pad margin}{pad padding}{term}"
  | center => let hp := if 1 &&& padding == 0
                        then padding >>> 1 else (padding + 1) >>> 1
              let mg := if 1 &&& margin == 0
                        then margin >>> 1 else (margin + 1) >>> 1
              s!"{acc}{pad hp}{pad mg}{term}{pad mg}{pad hp}"

def padRow (mw : Nat) (spec : PPSpec header) (t : Row header) (acc := "")
  : String :=
  let {align := as, width := ov,margin := mg,..} := spec
  match header with
  | [] => ""
  | [_] => if let some w := ov then withAlign acc t.render (w - t.length) mg as
           else withAlign acc t.render (mw - t.length) mg as
  | _ :: _ :: _ =>
    match ov with
    | (some w, ovs) =>
        padRow mw {spec with align := as.2, width := ovs} t.2
      $ withAlign acc t.1.render (w - t.1.length) mg as.1
    | (_, ovs) =>
        padRow mw {spec with align := as.2, width := ovs} t.2
      $ withAlign acc t.1.render (mw - t.1.length) mg as.1

def padHeader (mw : Nat) (spec : PPSpec header) (accl := 0) (acc := "")
  : String × Nat :=
  let {align := as, width := ov,margin := mg,..} := spec
  match header with
  | [] => ("", 0)
  | [x] => if let some w := ov
           then (withAlign acc x.render (w - x.length) mg as, mg + w + accl)
           else (withAlign acc x.render (mw - x.length) mg as, mg + accl)
  | x :: _ :: _ =>
    match ov with
    | (some w, ovs) =>
        padHeader mw {spec with align := as.2, width := ovs} (accl + w + mg)
      $ withAlign acc x.render (w - x.length) mg as.1
    | (_, ovs) =>
        padHeader mw {spec with align := as.2, width := ovs} (accl + mw + mg)
      $ withAlign acc x.render (mw - x.length) mg as.1

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
    s!"{name}\n{hd}\n{pad totl '='}\n{bd}"
  else bd

end PrettyPrint
