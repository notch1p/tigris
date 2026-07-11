import Tigris.TCNF.entrypoint

open TCNF

def cases : List (String × String) :=
  [ ("literal",          "42")
  , ("saturated prim",   "add 1 2")
  , ("partial prim",     "add 1")
  , ("curry saturate",   "let f x y = x in f 10 20")
  , ("curry partial",    "let f x y = x in f 10")
  , ("pap then app",     "let f x y = x in let g = f 10 in g 20")
  , ("pair",             "(1, 2)")
  , ("cond",             "if true then 1 else 2")
  , ("match lit",        "match 1 with | 1 => 10 | _ => 20")
  , ("match pair",       "match (1,2) with | (a,b) => a")
  , ("match in arg",     "add (match 1 with | 1 => 10 | _ => 0) 5")
  , ("nested match",     "match (1,2) with | (a,b) => match a with | 1 => b | _ => a")
  , ("match multi",      "match 1, 2 with | 1, y => y | x, _ => x")
  , ("let rec fac",      "let rec fac n = if __eqInt n 0 then 1 else mul n (fac (sub n 1)) in fac 5")
  , ("nonexhaustive",    "fun n => match n with | 1 => 10")
  , ("over-application", "let g y = y in let f x = g in f 1 2")
  , ("mutual rec",       "let rec ev n = if __eqInt n 0 then 1 else od (sub n 1) and od n = if __eqInt n 0 then 0 else ev (sub n 1) in ev 10")
  , ("shadowing",        "let x = 1 in let x = 2 in x")
  ]

def check1F (s : String) (E := MLType.defaultE) : IO Unit :=
  match Parsing.parse s initState with
  | .error e => println! e
  | .ok e    =>
    match runInferConstraintF e E with
    | .error e' => println! toString e' ++ s!"AST: {reprStr e}"
    | .ok    (fe, _, l) => do
      IO.println l
      let ir <- lowerToCode ∅ fe |>.toIO .userError
      println! Std.ToFormat.format ir |>.pretty (width := 40)

def main : IO Unit :=
  cases.forM fun (name, src) => do
    IO.println s!"\n══════ {name} :: {src}"
    check1F src MLType.defaultE'

-- #eval
--   check1F "let f x y = x in let g = f 10 in g 20"

-- #eval do
--   let s <- IO.FS.readFile "examples/list.tig"
--   checkModF s |>.toIO .userError

-- #eval do
--   let s <- IO.FS.readFile "examples/fact.tig"
--   checkModF s |>.toIO .userError

-- #eval do
--   let s <- IO.FS.readFile "examples/fun.tig"
--   checkModF s |>.toIO .userError

-- #eval do
--   let s <- IO.FS.readFile "examples/fun.tig"
--   checkCC s |>.toIO .userError

-- #eval do
--   let s :=
-- "
-- let classify n =
--   let rec ev k =
--         match k with | 0 => true  | _ => od (k - 1)
--   and     od k =
--         match k with | 0 => false | _ => ev (k - 1)
--   in (ev n, od n)

-- let main = classify 10
-- "
--   checkCC s |>.toIO .userError

-- #eval do
--   let s :=
-- "
-- let adder x = let g y = x + y in g

-- let sumTo n =
--   let rec go acc k =
--     match k with
--     | 0 => acc
--     | _ => go (acc + k) (k - 1)
--   in go 0 n

-- let main = (adder 10 5, sumTo 100)
-- "
--   checkCC s |>.toIO .userError
--   println! "-------------------------------------"
--   checkKOC s |>.toIO .userError


-- #eval main
