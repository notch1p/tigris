;; == System F IR ==

let i_C_0 : C Int = C@Int fun x : Int => x

let i_C_1 : C Bool = C@Bool fun _ : Bool => 5

let i_D_0 : D Int = D@Int fun x : Int => 100

let i_C_2 : [D a] C a =
  Λ a. fun d_D_0 : D a => C@a fun x : a => add (d_D_0[0, d]@a x) 1

let main : Int × Int =
  let rd_D_0 : D Int = i_D_0
  and rd_C_1 : C Int = Λ α. i_C_2@Int rd_D_0
  and rd_C_2 : C Bool = i_C_1
  in ⟨rd_C_1[0, c]@Int 1, rd_C_2[0, c]@Bool true⟩
