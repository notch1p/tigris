import Tigris.oldInterpreter.entrypoint

/-- info:
let z : Int = 3 and x : Int = add z 1
and w : Int = 4 and y : Int = add w 2
and main : Int = add x y
-/
#guard_msgs in
#eval MLType.checkFile $
"
let rec main = x + y
where
     x :=
  z + 1
     y :=
      w + 2
     z := 3; w := 4
"
example := x + y
where
     x :=
  z + 1
     y :=
      w + 2
     z := 3; w := 4
