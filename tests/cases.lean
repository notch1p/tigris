import Tigris.TCNF.interpreter.evalCEK

structure TestSpec where
  name         : String
  path         : System.FilePath
  expected     : String := ""
  interpreted  : TCNF.Interpreter.Value := .unit

open System.FilePath renaming mk -> fp, fileStem -> fn in
def execCases : Array TestSpec :=
--  sources                SBCL ~S output (normalized)       Interpreted Value (evalCEK.lean)
--                         empty to skip
 #[ (cases/"r1"            , r"(42 15 . 2)"                  , .pair
                                                                 (.int 42)
                                                                 (.pair (.int 15) (.int 2))  )
  , (cases/"tc"            , r"5050"                         , .int 5050                     )
  , (cases/"seq"           , r"6"                            , .int 6                        )
  , (cases/"expr"          , r"260"                          , .int 260                      )
  , (cases/"let"           , r"(1 . T)"                      , .pair (.int 1) (.bool true)   )
  , (cases/"nested"        , r"1"                            , .int 1                        )
  , (cases/"hkt-infer"     , r"#S(|c/Some| :|tag| 1 :|f0| 1)", .constr "Some" #[.int 1]      )
  , (examples/"runst"      , r"1"                            , .int 1                        )
  , (examples/"recinst"    , r"9"                            , .int 9                        )
  , (examples/"mutual"     , r"5"                            , .int 5                        )
  , (examples/"where"      , r"50"                           , .int 50                       )
  , (examples/"cont"       , r"42"                           , .int 42                       )
  , (examples/"fun"        , r"(40 . 60)"                    , .pair (.int 40) (.int 60)     )
  , (examples/"neg"        , r"-1"                           , .int (-1)                     )
  , (examples/"diamond"    , r"1"                            , .int 1                        )
  , (examples/"statem"     , r"(42 . 2)"                     , .pair (.int 42) (.int 2)      )
  , (examples/"recency"    , r"(101 . 5)"                    , .pair (.int 101) (.int 5)     )
  , (examples/"rankn"      , r"(1 . T)"                      , .pair (.int 1) (.bool true)   )
  , (examples/"rankn-app"  , r"(1 1 . 1)"                    , .pair
                                                                 (.int 1)
                                                                 (.pair (.int 1) (.int 1))   )
  , (examples/"typeclass0" , r"(3 . 1)"                      , .pair (.int 3) (.int 1)       )
  , (examples/"hkt-eta"    , r"#S(|c/Some| :|tag| 0 :|f0| 3)", .constr "Some" #[.int 3]      )
  , (examples/"let-gen"    , r""
                           , .constr "Mk" #[ .constr "Mk" #[.bool true, .bool false]
                                           , .constr "Mk" #[.bool true, .bool false]]        )]
  |>.map fun (p, s, v) => ⟨name p, p.addExtension "tig", s, v⟩
where examples := fp "examples"
      cases    := fp "tests" / "cases"
      name p   := fn p |>.getD p.toString
in open execCases in
def errorCases : Array TestSpec :=
 #[ (error/"inst"       , "Kind mismatch")
  , (error/"juxta"      , "Kind mismatch")
  , (error/"overapp"    , "Kind mismatch")
  , (error/"infer"      , "Can't unify")
  , (error/"amb2"       , "Can't unify")
  , (error/"amb"        , "Ambiguous: HEq")
  , (error/"recinst-fun", "Ambiguous: Eq (List")
  , (error/"imp6"       , "Can't unify")]
  |>.map fun (p, s) => {name := name p, path := p.addExtension "tig", expected := s}
where error := cases/fp "error"

def compileCases : Array TestSpec :=
 #[ "fact", "list", "opt", "op-let", "struct"
  , "typeclass4", "typeclass5", "typeclass6"
  , "hkt-dict-parametricity", "hkt-eager-specialize"
  , "poly-ref", "poly-ref-io", "poly-ref-io-safe"
  , "recinst"]
  |>.map fun n => {name := n, path := execCases.examples / n |>.addExtension "tig"}
