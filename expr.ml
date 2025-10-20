type 'a expr =
  | Atom of 'a
  | Add of 'a expr * 'a expr
  | Sub of 'a expr * 'a expr
  | Mul of 'a expr * 'a expr
  | Div of 'a expr * 'a expr

let rec eval = function
  | Atom a -> a
  | Add (e1, e2) -> eval e1 + eval e2
  | Sub (e1, e2) -> eval e1 - eval e2
  | Mul (e1, e2) -> eval e1 * eval e2
  | Div (e1, e2) -> eval e1 / eval e2


let prog =
  Mul ( Atom 20
      , Sub ( Mul (Atom 10, Atom 20)
            , Div ( Atom 2400
                  , Add ( Atom 120
                        , Add ( Mul (Atom 10, Atom 20)
                              , Atom 0)))))

let 3860 = eval prog
