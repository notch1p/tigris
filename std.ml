type 'a option = None | Some of 'a

let getOption (Some a) = a
let getOptionD a d =
  match a with | None -> d | Some a -> a
let mapOption f a = 
  match a with | None -> None | Some a -> f a

type 'a list' = Nil' | Cons' of 'a * 'a list'

let car (x :: _) = x
let cdr (_ :: xs) = xs
let rec map f = 
  function 
  | [] -> [] 
  | x :: xs -> f x :: map f xs
let rec foldl f xs init =
  match xs with 
  | [] -> init
  | x :: xs -> foldl f xs (f init x)

let rec foldr f xs init =
  match xs with
  | [] -> init
  | x :: xs -> f x @@ foldr f xs init

let foldl1 f xs =
  let rec go xs = 
    match xs with
    | [x] -> x
    | x :: y :: xs -> go (f x y :: xs)
  in go xs

let foldr1 f xs =
  let rec go xs = 
    match xs with
    | [x] -> x
    | x :: y :: xs -> 
      f x @@ go @@ y :: xs
    in go xs

let rec append xs ys =
  match xs, ys with
  | [], ys -> ys
  | x :: xs, ys -> x :: append xs ys

let (++) x y = append x y

let flip f x y = f y x

let rec bind f = function [] -> [] | x :: xs -> f x ++ bind f xs

let (=<<) xs f = bind xs f
let (>>=) f xs = bind xs f

let fst (x, y) = x
let snd (x, y) = y
let mapProd f g (x, y) = (f x, g y)
