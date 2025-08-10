let rec fact n = if n = 0 then 1 else n * fact (n - 1)

let fib n =
  let rec fib' n i j = 
    if n = 0 then i 
    else fib' (n - 1) j (i + j)
  in
  fib' n 0 1
;;

let rec ack m n =
  if m = 0 then n + 1 
  else if n = 0 then ack (m - 1) 1 
  else ack (m - 1) (ack m (n - 1))
;;

let compose f g x = f @@ g x

(* infixr 90 " . " -> fun f g x -> f (g x) NB. This is a comment in OCaml, but
                                           NB. is not in `hm.lean`
                                           NB. syntax for defining new infix operators:
                                           NB. (infixl | infixr) prec symbol -> expr
                                           NB.                   Int  String
   infixr 90 " ∘ " -> compose *)
let expt n base =
  let rec go n = 
    if n = 0 then 1 
    else base * go (n - 1) 
  in
  go n


let flip f x y = f y x

(* infixr 80 " ^ " -> flip expt *)

(* let exfalso = rec id  *)
