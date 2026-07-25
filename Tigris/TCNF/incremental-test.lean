import Tigris.TCNF.«entrypoint-incr»
open TCNF Incremental
/-- info:
let fn#18/2 (x#6 : Int, y#7 : Int) : Int → Int → Bool =
  let π#8 : Bool = EQⁱ(#6, #7); ret #8

let i_Eq_0#2/0 : Eq Int = let fn#5 : Int → Int → Bool = 𝐂⟦18⟧; ret #5

let rec sumTo#3/2 (n#10 : Int, acc#11 : Int) : Int → Int → Int =
  let app#13 : Bool = #18(#10, 0);
  case #13 of
    true => ret #11;
    false =>
      let π#14 : Int = SUB(#10, 1);
      let π#15 : Int = ADD(#11, #10); let app#16 : Int = #3(#14, #15); ret #16

let main#4/0 : Int = let app#17 : Int = #3(100, 0); ret #17
-/
#guard_msgs in #eval do
  let s <- IO.FS.readFile "tests/cases/tc.tig"
  EIO.toIO .userError $ checkKOC s

/--info:
let fn#8/2 (x#4 : Int, y#5 : Int) : Int → Int → Bool =
  let π#6 : Bool = EQⁱ(#4, #5); ret #6

let i_Eq_0#2/0 : Eq Int = let fn#3 : Int → Int → Bool = 𝐂⟦8⟧; ret #3

let rec sumTo#9/2 (n#10 : Int, acc#11 : Int) : Int → Int → Int =
  let app#13 : Bool = #8(#10, 0);
  case #13 of
    true => ret #11;
    false =>
      let π#14 : Int = SUB(#10, 1);
      let π#15 : Int = ADD(#11, #10); let app#16 : Int = #9(#14, #15); ret #16

let main#17/0 : Int = let app#18 : Int = #9(100, 0); ret #18
-/
#guard_msgs in #eval do
  let s <- IO.FS.readFile "tests/cases/tc.tig"
  EIO.toIO .userError $ checkKOCI s
