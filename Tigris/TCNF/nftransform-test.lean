import Tigris.TCNF.nftransform
open TCNF.Compiler

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

#eval
  check1F "let f x y = x in let g = f 10 in g 20"

#eval do
  let s <- IO.FS.readFile "examples/list.tig"
  checkModF s |>.toIO .userError

#eval do
  let s <- IO.FS.readFile "examples/fact.tig"
  checkModF s |>.toIO .userError

#eval do
  let s <- IO.FS.readFile "examples/fun.tig"
  checkModF s |>.toIO .userError

def main : IO Unit :=
  cases.forM fun (name, src) => do
    IO.println s!"\n══════ {name} :: {src}"
    check1F src MLType.defaultE'

#eval main
