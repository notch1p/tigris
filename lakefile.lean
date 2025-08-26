import Lake
open Lake DSL System

package "tigris" where
  version := v!"0.6.2"

@[default_target]
lean_exe "tigris" where
  root := `Main

input_file ffi.c where
  path := "c" / "ffi.c"
  text := true

target ffi.o pkg : FilePath := do
  let oFile := pkg.buildDir / "c" / "ffi.o"
  let srcJob <- ffi.c.fetch
  let weakArgs := #["-I", (<- getLeanIncludeDir).toString, "-I", "/usr/local/include", "-O3"]
  let cc := match <- IO.getEnv "CC" with | some CC => CC | none => "cc"
  buildO oFile srcJob weakArgs #["-fPIC"] cc getLeanTrace

lean_lib «Tigris» where
  precompileModules := true
lean_lib «PP» where
  moreLinkObjs := #[ffi.o]
  precompileModules := true


open IO.FS String in
target gen_compdb pkg : Unit := do
  let prefixp := pkg.buildDir / "c"
  let ( jsonp, artp ) :=
      ( pkg.dir / "compile_commands.json"
      , prefixp / "ffi.o.json")
  let srcJob <- inputTextFile <| pkg.dir / "c" / "ffi.c"
  let weakArgs := #["-I", (<- getLeanIncludeDir).toString, "-I", "/usr/local/include"]
  let cc := match <- IO.getEnv "CC" with | some CC => CC | none => "cc"

  unless <- FilePath.pathExists prefixp do createDirAll prefixp
  ( runBuild
  $ buildO
      artp srcJob weakArgs
      #["-fPIC", "-fsyntax-only", s!"-MJ{artp}"] cc getLeanTrace
  )
  *> pure Job.nil
  <* concatJsonWriteFile jsonp pkg where
concatJsonWriteFile (p : FilePath) pkg : LogIO Unit := do
  let dir := pkg.buildDir / "c"
  let jsons := (<-dir.walkDir).filter λ path =>
    path.toString.endsWith r".o.json"

  let cat_json <- jsons.foldlM (init := "") λ acc path =>
      readFile path >>= pure ∘ (· ++ acc)

  logInfo $ reprStr jsons
  liftM <| pure s!"[{dropFirstRight cat_json (· == ',')}]" >>= writeFile p

dropFirstRight (s : String) (p : Char -> Bool) : (r : _ := endPos s) -> String
  | ⟨0⟩ => s
  | pos@⟨next + 1⟩ =>
    if p $ s.get pos then s.set pos ' '
    else dropFirstRight s p ⟨next⟩
  termination_by r => r.1

extern_lib libleanffi pkg := do
  let ffiO <- ffi.o.fetch
  let name := nameToStaticLib "leanffi"
  buildStaticLib (pkg.staticLibDir / name) #[ffiO]

require Parser from git "https://github.com/fgdorais/lean4-parser"@"617f4fa5c48f35076274d57546884261560f1285"
