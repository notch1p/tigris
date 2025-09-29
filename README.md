# tigris

<p><a href="https://commons.wikimedia.org/wiki/File:Panthera_tigris_tigris.jpg#/media/File:Panthera_tigris_tigris.jpg"><img src="https://upload.wikimedia.org/wikipedia/commons/4/49/Panthera_tigris_tigris.jpg" alt="File:Panthera tigris tigris.jpg" height="428" width="640"></a><br>By Hollingsworth, John and Karen, retouched by <a href="//commons.wikimedia.org/w/index.php?title=User:Zwoenitzer&amp;action=edit&amp;redlink=1" class="new" title="User:Zwoenitzer (page does not exist)">Zwoenitzer</a> - Fish &amp; Wildlife Service (ID WO0409-33F <a rel="nofollow" class="external autonumber" href="https://images.fws.gov/default.cfm?fuseaction=records.display&amp;CFID=2521090&amp;CFTOKEN=51847147&amp;id=1EF5BD3B%2D531E%2D4B70%2D9E0CC00D5AB77EA5">[1]</a>), Public Domain, <a href="https://commons.wikimedia.org/w/index.php?curid=39197">Link</a></p>

## artifacts

check CI pages for pre-built binary, IR, generated C source and libraries.

## Synopsis

it looks like a hybrid of OCaml & Haskell & Lean,

> [!WARNING]
> But runs like shit.

thanks to

- actual currying,
- pattern matching is worst case $\mathcal{O}(mn)$ for pattern matrices of shape $m\times n$,
- ~~no decision tree~~ (technically there is one in [matchApp](Tigris/core/matchApp.lean), but not used)
- ~~no exhaustiveness check~~
- ~~zero optimization~~ (IR has some optimization, interpreter no) for maximum ease of reason,
- various canonical but inefficient translations of certain constructs
- and a naive term-rewriting interpreter.

## implementation details

### on parsing

there are 2 parser implemetations:

- `pratt` branch, use a simplified version of pratt parser (i.e. without per-side binding power)
- `master` branch, use a easy-to-reason precedence-climbing-like parser based on `chainl1` `chainr1`, also uses a stack machine similar to shunting-yard.
  Rebuilds the parser based on the operator precedence table on-the-fly and at every call to `parseExpr`.

The second one is quite inefficient as caching the parser is essentially impossible because if we were to cache the parser in the state then between the state and the parser monad `TParser` exists a cyclic dependency.
While Lean does allow mutual recursion on types (also used in the evaluator: `VEnv` and `Value`),

- for `abbrev/def` type definition we won't pass the termination analysis
- for inductive type because `TParser` is a function type and due to the strict positivity that Lean kernel poses it's not going to pass typechecking either.
- Even though the type, from a programming perspective, is unproblematic.
- `unsafe` is always an option, but type-level `unsafe` cannot be evaded with `implemented_by` for obvious reasons so it's very infective
- and personally I'm not a big fan of marking _every_ definitions in this repository `unsafe`.

### on pretty printing

- there is an dependently typed table printer inside `PP` that I cherry picked out of the undermentioned repository.

the design of the implementation is based on the understanding that a table depends on its header.

In practice, tables with different headers have different types (hence the dependency), two tables are of the same type if they share the same (in the sense of definitional equality) header.

This way we _almost_ require all headers and the number of columns a table has to be known compile-time, effectively fixing the shape of the table because
a row is captured in a product, whose type (subsequently, size) is dependent on the header (So in reality it's more of a `List`, but dependent) but is visible to the typechecker unlike `List` or `Array`.
`Vector` is also possible, but it doesn't feel natural to use because unlike products it lacks the `List`-like inductive reasoning.

Additionally it allows all kinds of table in the source to be properly organized.

### on the FFI

- this has been in the undermentioned repo for a very long time.
- Dates back to the times that Lean was still new to me, and as a result of testing Lean's FFI interface.

Functions that are implemented with Lean-C interop:

- `Char.repeat` -- repeats a char. we use regular loop for Unicode,`memset` for ASCII chars, much faster in latter case.
- `setStdoutBuf` -- enable/disable stdout buffering. Although I'm not sure whether this actually works, since Lean didn't provide this function (at least I haven't found it), I implemented it myself.

### on that axiom inside [parsing/types.lean](Tigris/parsing/types.lean)

- Used in `transformPrim` from [utils.lean](Tigris/utils.lean)
  (same situation, I'm suspecting this something to do with nested inductive types i.e. in the `Match` branch, we use array to store match discriminants)

Any constructivist (or Anyone, really) probably isn't a fan of blatantly importing axioms.

It's undesirable, I know.

But proving the transformation function terminates amounts to finding a decreasing measure that decreases according to the _foundational_ (wellfounded, in set theory sense) relation on the type of such measure. In this case it's `SizeOf Expr`.

it's all fun and joy until we have to prove the obvious fact:
(because our array carries `Pattern × Expr`, technically we only need the RHS of that logic and)

$$
\forall p:\ \alpha\times\beta, \mathsf{sizeOf}\ (\pi_1\ \ p) < \mathsf{sizeOf}\ p\ \land\ \mathsf{sizeOf}\ (\pi_2\ \ p) < \mathsf{sizeOf}\ p
$$

Do note the difference between the following:

```lean
example {p : α × β} : sizeOf p.1 < sizeOf p ∧ sizeOf p.2 < sizeOf p := ⟨Nat.lt_add_one _, Nat.lt_add_one _⟩

example {p : α × β} [SizeOf α] [SizeOf β] : sizeOf p.1 < sizeOf p ∧ sizeOf p.2 < sizeOf p := ...?
```

Without the `SizeOf` constraint the `sizeOf` instance of `α` and `β` defaults to the dummy instance `instSizeOfDefault` which always return 0.
You can't really use that to prove anything (other than the above ofc).

We can't prove the second one because although Lean automatically generates `SizeOf` instance for every inductive type, we can't really unfold it.
One might think that if we instantiate the type variables above with concrete types (in our case, respectively, Pattern and Expr.)
we might be able to prove it, but no. Lean still doesn't unfold the generated definition.

One might also think that we'd still have a chance if we directly define the `SizeOf` of a pair to be the sum of every component plus 1.
After all that is the expected behavior according to the documentation and source code and matches the one generated. i.e.

```lean
instance [SizeOf α] [SizeOf β] : SizeOf α × β where
  sizeOf p := sizeOf p.1 + sizeOf p.2 + 1
```

That works (in proving the above), but currently I've found no way to make WF recursion use the one we manually implemented so in reality we can't make
use of this one in our termination proof.

I still choose to import the aforementioned prop as an axiom instead of marking recursive function that depends on this fact partial is because it's trivial and it's just as obvious as
proving those functions terminates.

> overall this shouldn't be a huge problem because the behavior described in the axiom is intended.

### what about (...)

#### IR/Backends

We currently maintain a two stage IR for the ease of reasoning:

- IR₀: Lambda IR
- IR₁: CPS IR

- Pipeline

  1. Lambda IR (ANF)
     1.1 Uncurrying
     1.2 Pattern matching lowering via decision tree
     1.3 Closure Conversion
     1.4 Optimizations
  2. CPS IR
     2.1 optimizations
  3. Common Lisp

- [x] Frankly I'm not very familiar with backends, Even If I were to do it,
      it would most likely be a example of compiling with continuations,
      with optional ANF transformation, closure conversion (already done),
      ~~and defunctionalization.~~

- there is a experimental IR at [core](Tigris/core) that translates to an ANF first:

  - see [core/lam.lean](Tigris/core/lam.lean) for the IR spec.
  - with pattern matching compilation to (light) decision tree
    (also contains a backtraking automata, not used.)
    - "light" in the sense that we do not perform exhaustiveness check at this level.
      Because it is done at typechecking, together with redundantness check
      (redundant rows are removed immediately upon detection).
      We then reuse the results directly to compile pattern matching.
  - basic optimizations have been done, including:
    - constant folding/propagation
    - copy propagation, with dead code elimination (including eta-reduction) after
    - tailcall
  - closure conversion [core/lift.lean](Tigris/core/lift.lam)
    are done at the end of this pass.

- ~~no codegen yet.~~

- there is a naive CPS IR at [cps](Tigris/cps). It doesn't do much, but
  non-tailrec functions are transformed to CPS to maintain tailrec property.

  - also contains some optimizations

- there is a common lisp backend. Basically a 1-to-1 translation of CPS IR.

  - Why common lisp? Because I'm familiar with the langauge.
  - Although the Lisp-2 double namespace (value/function) does add complexity to
    the codegen process.
  - Virtually all functions are tailrec however SBCL does not guarantee tailrec optimization
    that means we are at the mercy of SBCL's optimizer. _Trust the compiler_.
  - an `extern` definition whose syntax is

    ```ebnf
    <extern-decl> ::= "extern" <id> <strlit> ":" <type-scheme>
    <type-scheme> ::= (("forall" | "∀") <id>+ ,)? <type-exp>
    ```

    can be used to add import foreign functions.
    Although this is merely a syntactic transformation and it doesn't "just work".
    You'll need to follow the calling convention found in [core/lift.lean](Tigris/core/lift.lean) and
    [codegen/sbcl.lean](Tigris/codegen/sbcl.lean) to define those functions in the runtime.

    - see also [ffi.lisp](ffi.lisp) for examples

This part (IR/Backends) is somewhat better documented than others, because I'm not that
familiar with compiler backends and codegen.

#### Exhaustiveness/Redundant check

- [x] Planned, if I'm going to do it then it would be very similar to \[Maranget2007\][^1]
      , just like OCaml.

Has done the very barebone.
It's an almost one-to-one implementation of the algorithm described in the paper above.

#### higher-kinded type

- [x] somewhat done. A bit restrictive: bound type ctor is not curried and must
      be fully applied

although there isn't any kind inferrence and type declaration parsing
depends on the arity of type constructors.

- arity must be provided to bind a type constructor, otherwise default to 0.
- A simplified notation `(id : n)` that is
  analogous to Haskell's 1-universe notation `* -> *` or Lean's `Type 0 -> Type 0`

the full syntax is

```ebnf
<ty-decl> ::= "type" <ty-params> "=" <ctor-def>"|"+
<ty-params> ::= <id> | (<id>) | (<id> ":" <int>)
```

#### Typeclass/Constraints

- [ ] Planned. if I'm going to do it then it would be a dictionary passing implementation.
- because there isn't any memoization of values this implementation will not impose monomorphism restriction found in Haskell (On a separate note: as there's currently no side effects such as mutable references, we are free from value restriction as well).

currently primitive polymorphic functions that should be constrained (e.g. homogeneous equality) is done directly
in the interpreter (somewhat akin to a dynamically typed `(· = ·)`):
looking up tags inside values at runtime then dispatching to correct monomorphic implementations.

For values (including constructors) of function type, an error is thrown as equality handlers for
these values aren't implemented (and likely never will).

One could argue that theoretically we could implement
an intensional (syntactic) approach by transforming their AST to normal forms and compare them
with the equality relation on `Expr`, as is the case in Lean (besides `funext`).

But This is unlikely to be done because I've decided it's too elaborate and metatheoretic.

- **25.09.30** we are getting there.

## Specification

See source.

## Evolution

This project is a pain in the ass to develop and has undergone multiple refactors (but ultimately sloppy) because of my shortsighted project planning.

1. Somewhere during pre-historic times, I decided to try out Lean as a programming language
   , besides having prior experiences with it only as a theorem prover. (also familiar with Coq at that time).
2. a handwritten parser for a tiny ML-like langauge + Hindley-Milner type system implementation
   (w/ Algorithm W) became one of my earliest actual projects written in Lean.
3. Someone developed a parser combinator
   (nice work [fgdorais/lean4-parser](https://github.com/fgdorais/lean4-parser)).
   Switched to it, refactor #1.
4. Revisiting the project: added a term-rewriting based interpreter, refactor #2.
5. added recursion
   ~~(mutual recursion not yet supported to this day, which sadly also requires a huge refactor)~~ Done.
   , refactor #3
6. added toplevel declaration, refactor #4.
7. added pattern matching together with algebraic datatypes, mutual recursive types,
   also need to support toplevel type binding, refactor #5.

   - ~~funny how mutual recursion hasn't been added but mutual rectype has.~~ Done.
   - mutual recursion and mutual rectypes have different syntax:

     - mutual recursion: OCaml-like `let rec ... and ... in ...`

       - although they aren't the same especially in terms of
         [shape restriction](https://ocaml.org/manual/5.3/letrecvalues.html#s:letrecvalues) of rhs
       - Our parser uses a basic heuristic to check the shape of rhs; typechecker handles a let-group
         in predefined order: function definitions first, then value.
         (this is given by our heuristic method: we check whether the shape of a rhs is a `Fun`.)
       - This means there is no order-preserving of `let ... and ...` definitions.
       - Though it seems that this way we don't need OCaml's shape restrictions
         or F#'s init-soundness checking as Tigris is simple enough.

     - mutual rectype: Lean-like `mutual <ty-decl>+ ;;` (mandatory `;;`)
       forward declaration is only allowed in a `mutual` block.

8. added toplevel pattern binding, refactor #6.
   - leaking slopiness: I didn't merge identifier binding with pattern binding (w/ PVar)
     and these 2 coexists.
9. added exhaustiveness/redundancy check for pattern matrices.
10. optimized parser performance with path cutting (`let` variants), better error reporting. refactor #7
11. added an experimental flat CPS IR, together with a decision tree pattern matching compiler.
    - directly translates from `Expr`, which performs rather poorly, and is known to be buggy.
    - There's a misplaced callsite issue due to static continuation and my implementation.
    - I've switch to a dynamic continaution which pattern matches on them and then dispatch to the correct one.
    - As expected it sucks performance/maintainability-wise
    - It is now living in `oldcore` and will always be for the rest of its life.
12. added a new "lambda" IR as the first half of a 2-stage IR. refactor #8.
    (like the namesake small language used as an IR for SML from Compiling with Continuation (Appel92))
    - have done various optimizations. these can be found in [opt.lean](Tigris/core/opt.lean)
    - Closure Conversion (lambda lifting, not in a strict sense: we've only made closure explicit) is done at the end of this process
      (also embedded some optimizations).
    - This IR will then gets compiled to a later-stage CPS IR.
    - It is now living in `core`.
    - both `oldcore` `core` have backtracking automata/decision tree implementation of pattern matching:
      - for `core`: decision tree is used.
      - for `oldcore`: backtracking automata is used.
13. from that point we'll do codegen. As for the target, I'm thinking of common lisp (SBCL esp).
    - which is the second most proficient language I'm in,
    - besides Lean (which has really become my most proficient and favorite language.), OCaml and Haskell.
14. but before that, I'm also tempting to add new features like typeclass and ~~mutual recursion (highest priority)~~ (I literally supported it after writing down this README)
    - which, sadly, will require another refactor at both
      - `Expr` (because I'll need a letrec group), and subsequently, everything relating to it (basically the entire project)
      - typechecker. While it is possible to add new layers on the existing Algorithm W to achieve constraints,
        it is not very maintainer-friendly to do so. Ultimately I'm afraid we'll have to switch to a constraint-solving based implementation.

- Bonus: There's a _DTigris_ variant in development with Haskell which uses dependent type (single universe unfortunately).

## History

- 25/08/10 taken out of [notch1p/Playbook](https://github.com/notch1p/lean-snippets)

[^1]: [Maranget, Luc. "Warnings for pattern matching." Journal of Functional Programming 17.3 (2007): 387-421.](http://moscova.inria.fr/~maranget/papers/warn/warn.pdf)
