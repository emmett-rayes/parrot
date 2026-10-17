# AGENTS.md — Parrot

Guidance for AI coding agents working in this repository. Read it fully before changing code: the project is small but
very dense, it leans on experimental Scala 3 features, and its conventions are strict and consistent.

---

## 1. What Parrot is

Parrot is a **parser-combinator library derived from category theory**, written in Scala 3.

- `parrot.category` is a self-contained, dependency-free library of type classes for categorical structures
  (functors, monads, profunctors, promonads, monoidal/cartesian/cocartesian/closed categories, traces, Conway and Elgot
  fixed-point operators, restriction categories, enrichment, …), each with its **laws encoded as executable code**.
- `parrot.parser` defines an abstract **`ParserAlgebra`** (the combinator interface) and derives every combinator from
  one of those categorical structures through small mixin traits. Two interpreters exist:
  - **`ReferenceParser`** — the executable *specification*: a Kleisli promonad over `StateT[Input, Try]`.
  - **`StrictParser`** — an *optimizing* interpreter that reifies parsers as an AST (`Node`) over reified pure
    functions (`Fn`), normalizes them at construction time, and runs them with a mutable state and no boxing.
- `parrot.json` contains `JsonGrammar`, a JSON grammar written once against *any* standard `ParserAlgebra`, used as the
  main end-to-end test and benchmark workload.

There is no `main` application, no runtime dependency, and no published artifact. The only dependencies are
ScalaTest and ScalaCheck, in `Test` scope.

---

## 2. Toolchain and commands

| Item         | Value                                                      |
| ------------ | ---------------------------------------------------------- |
| Scala        | `3.9.0` (`build.sbt`)                                      |
| sbt          | `2.0.10` (`project/build.properties`) — **sbt 2**, not 1.x |
| JDK          | developed on OpenJDK 25                                    |
| Formatter    | scalafmt `3.11.3` (`.scalafmt.conf`), no sbt plugin        |
| sbt plugins  | only `sbt-ide-settings` (IntelliJ)                         |
| Test libs    | ScalaTest `3.2.20`, scalatestplus `scalacheck-1-19`        |

Commands (run from the repository root; `--client` reuses a running sbt server and is much faster):

```sh
sbt --client compile                     # compile main
sbt --client Test/compile                # compile main + tests
sbt --client testFull                    # run ALL tests (25 suites, ~263 tests, a few seconds)
sbt --client test                        # sbt 2: INCREMENTAL (= testQuick) — may run nothing!
sbt --client "testOnly parrot.parser.StrictParserTest"
sbt --client "testOnly parrot.category.*"
sbt --client "Test/runMain parrot.json.JsonBenchmark [--reference] [suite ...]"
```

Important sbt 2 gotchas:

- **`test` is incremental in sbt 2** (it behaves like `testQuick` and prints "No tests to run" if nothing changed).
  Use **`testFull`** whenever you need to know the whole suite passes.
- sbt 2 caches compilation outputs; `clean; compile` can be served from cache and complete in a couple of seconds.
- `Test/runMain` forks. `JsonFixtures` resolves `src/test/resources/json` **relative to the working directory**, so
  always run from the repository root.

Benchmark suites: `json-test-suite`, `json-dummy-data`, `json-benchmark`, `nativejson-benchmark` (all if none given).
Only `StrictParser` is measured unless `--reference` is passed; `ReferenceParser` is very slow on the large documents.
Example: `sbt --client "Test/runMain parrot.json.JsonBenchmark nativejson-benchmark"` (≈ 85 MiB/s for `StrictParser`
at the time of writing). Use it to check for performance regressions after touching `StrictParser`, `Scanner`,
`CharSet` or `Fn`.

### Compiler flags (from `build.sbt`, mirrored in `.idea/scala_compiler.xml`)

```
-source:future -preview
-language:experimental.modularity          # `A is TC`, `type Self`, named/deferred givens, `tracked`
-language:experimental.pureFunctions
-language:experimental.genericNumberLiterals
-language:strictEquality                   # == needs CanEqual
-Yexplicit-nulls                           # Java APIs return T | Null
-Wunused:all -Wvalue-discard -Wnonunit-statement -Wsafe-init
-deprecation -feature -unchecked -explain -explain-types
```

These flags shape the code everywhere — see §7. **Keep the build warning-free**; warnings are not fatal, but the
codebase currently has none and every convention below exists to keep it that way. If you change flags in
`build.sbt`, mirror them in `.idea/scala_compiler.xml`.

---

## 3. Repository layout

```
build.sbt, project/                sbt 2 build (idePackagePrefix := "parrot")
.scalafmt.conf                     scalafmt 3.11.3, dialect scala3Future, maxColumn 120
src/main/scala/
  category/   (package parrot.category)   26 files — categorical type classes + laws + instances
  parser/     (package parrot.parser)     15 files — ParserAlgebra, mixins, interpreters, Fn, Scanner, CharSet
  json/       (package parrot.json)        JsonGrammar
src/test/scala/
  category/   one *Test per type class + CategorySuite (shared base)
  parser/     ReferenceParserTest, StrictParserTest, ScannerTest
  json/       JsonGrammarTest, JsonFixtures, JsonBenchmark (a `main`, not a test suite)
src/test/resources/json/           vendored JSON corpora (see README.txt there for upstream sources/commits)
  json-test-suite/                 nst/JSONTestSuite test_parsing (y_/n_/i_ prefixes)
  json-dummy-data/                 Microsoft Edge dummy data (64KB … 5MB, pretty and -min)
  json-benchmark/                  TkTech/json_benchmark samples
  nativejson-benchmark/            miloyip/nativejson-benchmark data + jsonchecker pass/fail
docs/, .agents/skills, .gemini/skills, .ai/mcp   currently empty
.idea/                             partially tracked IntelliJ config (code style, compiler profile, dictionary)
```

**Package/directory mismatch is intentional.** Because of `idePackagePrefix := Some("parrot")`, sources live in
`src/main/scala/<pkg>/` but declare chained package clauses:

```scala
package parrot
package category
```

Always use this two-clause header in new files (never `package parrot.category`, never a `parrot/` directory). The
chained form puts `parrot.*` in scope, which is why files write `import category.*` / `import parser.X` rather than
fully-qualified imports.

Never commit `target/`, `.bsp/`, or the untracked `.idea` files (see `.gitignore`). Don't edit the vendored JSON
fixtures; they are byte-exact copies of upstream corpora (some are deliberately invalid UTF-8 or malformed).

---

## 4. Architecture: `parrot.category`

### 4.1 The type-class encoding (read this first)

All type classes use Scala 3 **modularity**: a type class is a trait with an abstract `type Self` (or `Self[_]`,
`Self[_, _]`), and `A is TC` means `TC { type Self = A }`.

```scala
trait Promonad extends Profunctor {
  type Self[_, _]
  def unit[A, B](f: A ==> B): A ~> B
  def multiply[A, B, C](q: B ~> C, p: A ~> B): A ~> C
  ...
}
given FunctionIsPromonad: Function is Promonad { ... }
```

Recurring patterns — follow them exactly when adding or editing type classes:

1. **Local type aliases**: each trait gives `Self` a short `final type` alias used in signatures:
   `F` (Functor/Valued), `M` (Monad, Monoid), `~>` (Profunctor's `Self`), `==>` (the underlying category `On`),
   `*` (Monoidal `Tensor`), `+` (Cocartesian coproduct = `Tensor`), `^` (Closed `Exp`, flipped: `B ^ A = Exp[A, B]`),
   `P` (Enriched / ParserAlgebra), `V` (`Over` / Pointwise `Self`).
2. **Superstructure via named context bounds on the abstract `Self`**, re-exposed as a `val`:
   ```scala
   trait Cartesian extends Monoidal {
     override type Self[_, _]: Promonad as CartesianPromonad
     override val SelfIsPromonad: Self is Promonad = CartesianPromonad
     import SelfIsPromonad.*          // brings ~>, >>>, identity, … into scope
   ```
   The `<Name><Super>` given (e.g. `CartesianPromonad`, `ElgotCocartesian`, `ZippingStrong`) is a *deferred given*.
   The `SelfIs<Super>` / `OnIs<Super>` / `InIs<Super>` val is how members and other code reach the structure.
3. **Instances override both, with singleton types** (commit "switched to named context bounds with singleton given
   overrides"). Singleton types keep type members (`I`, `Tensor`, `On`, …) visible to the compiler:
   ```scala
   given FunctionIsCartesian: Function is Cartesian {
     type I      = Unit
     type Tensor = Tuple2
     override given CartesianPromonad: Promonad.FunctionIsPromonad.type = Promonad.FunctionIsPromonad
     override val SelfIsPromonad: Promonad.FunctionIsPromonad.type      = Promonad.FunctionIsPromonad
     ...
   }
   ```
   Some generic instances only override the given (the val defaults to it); when in doubt, override both.
4. **Instance naming**: `<Carrier>Is<TypeClass>` — `OptionIsMonad`, `KleisliIsElgot`, `FunctionIsLazyCartesian`,
   `CartesianIsSymmetric`, `ConwayIsCartesianTraced`. Every given is named (avoids clashes, enables explicit `using`).
   Instances live in the type class's companion object (or the carrier's companion, e.g. `Kleisli`, `StateT`, `Fn`,
   `Node`).
5. **Companion summoner**: `def apply[P[_, _]: TC]: P is TC = summon`.
6. **Type refinement helpers** in companions, used to pin type members in context bounds:
   - `Profunctor.on[P, T]` / `Monoidal.on` / `Cartesian.on` — fix the underlying category (`On`) to `T`.
   - ``Monoidal.`with`[U, T]``, ``Cartesian.`with`[U, T]``, ``Cocartesian.`with`[Z, T]``, ``Closed.`with`[U, T, E]``,
     ``Conway.`with` ``, ``Elgot.`with` `` — fix unit/tensor (and exponential).
   - `Strong.on[K, U, T]`, `Traced.on[K, U, T]` — fix underlying monoidal category.
   - `Monoid.in[K, U, T]`, `Comonoid.in`, `Fixed.in[K, U, T, E]` — fix the ambient monoidal category of an object.
   - `Enriched.over[E, V]`, `Valued.over[E, V]` — fix the target category **V** (itself a type class like
     `Monoid.Additive`).
7. **Extension methods**: each operation `op(self, …)` has an infix extension with `@targetName("opExt")` that
   delegates to `Trait.this.op(...)`, plus optional symbolic aliases. Nullary extensions that would clash with the
   method take `(using DummyImplicit)` (e.g. `restrict`, `dagger`, `left`, `right`, `flatten`).
8. **`export`** is used to forward an existing instance's members while overriding a few (see
   `Symmetric.FunctionIsSymmetric`, `Cartesian.CartesianIsSymmetric`).
9. **Deferred givens**: `given HomIsV: [A, B] => ((A ~> B) is V) = deferred` (Enriched), `FIsV` (Valued),
   `FunctionIsV` (Pointwise).
10. **Laws**: every type class has a nested `object <Name>Laws` whose methods return `Boolean` and take
    `(using X is Eq)` for the types they compare. Each law's scaladoc states the equation in math notation. Laws are
    *checked in tests*, not enforced by types.

### 4.2 Catalogue of type classes

| File | Structure | Key ops / notes | Instances |
| --- | --- | --- | --- |
| `Eq` | equivalence on `Self` | `eq`, `===` | `=:=`, any `CanEqual` type, `Try` (all failures equal) |
| `LazyTuple2` | by-name pair (`Product2`) | used as the *lazy* cartesian product | — |
| `Functor` | endofunctor on **Type** | `map` | `Option`, `Try` |
| `Monad` | monad (`Self[_]: Functor`) | `unit`, `flatten`, `flatMap` | `Option`, `Try` |
| `Profunctor` | **C**^op × **C** → **Type**; `type On[_, _]: Promonad` is **C** | `dimap`, `lmap`, `rmap` | `=:=`, `Function` |
| `Promonad` | monoid in endoprofunctors = a category | `unit` (η), `multiply` (μ), `identity`, `compose`, `andThen`, `<<<`, `>>>` | `=:=`, `Function`, `PartialFunction` |
| `Monoidal` | monoidal structure on a promonad | `tensor`/`***`, unitors, `associate`/`unassociate` | `Function` (Unit, Tuple2) |
| `Symmetric` | braided symmetric monoidal | `braid`; derives ρ, α⁻¹ | `Function`; derived from any Cartesian/Cocartesian |
| `Cartesian` | products | `augment` (!), `first`, `second`, `product`/`&&&`, `diagonal` | `Function`×`Tuple2`, `FunctionIsLazyCartesian` (×`LazyTuple2`); every object is a `Comonoid` |
| `Cocartesian` | coproducts (`Z`, `+`) | `absurd`, `left`, `right`, `sum`/`\|\|\|`, `fold`, `+++` | `Function`×`Either`; every object is a `Monoid` |
| `Closed` | internal homs | `eval`, `curry`, `uncurry` | `Function` (strict and lazy) |
| `Strong` | tensorial strength of a profunctor | `first`, `second` | `Function` (strict, lazy), Kleisli |
| `Traced` | trace (feedback) | `left`, `right` | `Function` lazy-cartesian (knot-tying), cocartesian (tail-recursive loop) |
| `Conway` | parameterized fixed point on a cartesian promonad | `dagger` | lazy `Function`; ⇄ cartesian `Traced` |
| `Elgot` | iteration on a cocartesian promonad | `dagger` | `Function`, Kleisli of Elgot monads; ⇄ cocartesian `Traced` |
| `Fixed` | unparameterized fixed points of an object in a CCC | `fix`, `fixTr` | exponentials `E[A, B]` (`ExponentialIsFixed`), `FunctionIsFixed`, `Tuple2IsFixed` (Bekić) |
| `Monoid` | monoid object in a monoidal category | `unit`, `multiply`; `Additive` (`zero`, `plus`, `+`), `Multiplicative` (`one`, `times`, `*`) | Additive: `Option` (orElse), `Try` (orElse), `Set` (union), functions pointwise; Multiplicative: `Int`, functions |
| `Comonoid` | comonoid object | `zero`, `add` | via `Cartesian.TIsComonoid` |
| `Restriction` | restriction category | `restrict` (f̄) | `Function` (trivial), `PartialFunction`, Kleisli of restriction monads |
| `RestrictionMonad` | monad with restriction | `restrict: M[A] => M[Unit]` | `Option`, `Try`, `StateT` |
| `ElgotMonad` | monad with iteration | `iterate` | `Option`, `Try`, `StateT` |
| `Enriched` | hom-sets live in **V** | `HomIsV`, `MonoidEnrichedLaws` | Kleisli over `Fixed`, Kleisli over a `Valued` **V** |
| `Valued` | functor whose values live in **V** | `FIsV` | `Try` over `Monoid.Additive`, `StateT` |
| `Pointwise` | **V** closed under `A => _` | `FunctionIsV` | `Monoid.Additive`, `Monoid.Multiplicative` |
| `Kleisli` | `type Kleisli[F[_]] = [A, B] =>> A => F[B]` | | Profunctor, Promonad, Strong, Cocartesian, Restriction, Elgot, Enriched over Fixed / Valued |
| `StateT` | `type StateT[S, M[_]] = [A] =>> S => M[(result: A, state: S)]` (named tuple) | | Functor, Monad, Valued, RestrictionMonad, ElgotMonad |

Laziness matters: the *lazy* cartesian structure (`LazyTuple2`) is what makes knot-tying fixed points (`Conway`,
`Traced`, `Fixed`) productive under strict evaluation. `Fixed.ExponentialIsFixed` uses the η-expanded dagger of
evaluation for exactly this reason (see its scaladoc). Don't "simplify" these to strict tuples.

### 4.3 Known deliberate subtleties

- `Try` is an additive monoid only **up to `Eq.TryIsEq`** (all failures identified); documented on
  `Monoid.Additive.TryIsAdditive`.
- `Comonoid.In` and `Monoid.in` currently only support `Function` as the base promonad (comment in `Monoid.in`).

---

## 5. Architecture: `parrot.parser`

### 5.1 `ParserAlgebra` — the interface

`trait ParserAlgebra` (in `ParserAlgebra.scala`) is a type class over `Self[_, _]` (alias `P`). A parser `P[A, B]`
consumes a prefix of the input while turning a **semantic input** `A` into a **semantic result** `B`.

Abstract type members that interpreters fix:

| Member | Meaning | Standard choice |
| --- | --- | --- |
| `On[_, _]` (alias `==>`) | pure functions on semantic values | `Function` (Kleisli) or `Fn` (Strict) |
| `Empty` | empty semantic value | `Unit` |
| `Pair[_, _]` (alias `*`) | pairs | `Tuple2` |
| `None` | impossible value | `Nothing` |
| `Alternative[_, _]` (alias `+`) | tagged alternatives | `Either` |
| `Many[_]` | collections | `Vector` |

`ParserAlgebra.Standard` is the refinement with exactly those standard choices; `JsonGrammar` and the agreement tests
are written against it.

> ⚠️ **`None` is shadowed** inside any `ParserAlgebra` (and its subclasses/importers): it is the *type member*. Use
> `scala.None` for `Option`'s `None` there (see `StrictParser`, `JsonGrammar`, tests). Likewise in `StrictParser`
> `Success`, `Failure`, `Seq`, `Pair`, `Merge`, … are `Node` cases; `Try`'s are imported as `TrySuccess`/`TryFailure`.

Combinators (each has an infix extension and many a symbolic alias):

| Method | Alias | Meaning |
| --- | --- | --- |
| `rule(p, label)` | | name for diagnostics (error label at start offset) |
| `literal(s)`, `regex(r)` | | primitives, `P[Empty, String]` |
| `pure(f)`, `success` | | no input consumed |
| `map(p, g)`, `mapInput(p, f)` | | post/pre-compose a pure function |
| `andThen` | `>>` | sequential composition (result feeds next semantic input) |
| `zip` | `**` | `P[A*C, B*D]` |
| `pair` | `&&` | same semantic input, pair results |
| `skipThen` / `thenSkip` | `*>` / `<*` | keep right / left result |
| `between(p, open, close)` | | |
| `branch` | `++` | `P[A+C, B+D]` |
| `merge` | `\|\|` | `P[A+C, B]` (copairing) |
| `failure` | | always fails |
| `orElse` | `\|>` | PEG ordered choice with backtracking |
| `or` | `+>` | ordered choice, tagged `B + C` |
| `optional` | | `self +> success` (derived) |
| `lookahead` | unary `~` | positive lookahead |
| `not` | unary `!` | negative lookahead (derived; StrictParser overrides) |
| `iterate` | | Elgot loop on `P[A, B + A]` |
| `repeated`, `times(n)`, `atLeast(n)`, `separatedBy(sep)` | | collect into `Many` |
| `recursive(f)` | | fixed point of `P[A, B] => P[A, B]` |
| `recursive[T <: Tuple](f)` | | `inline`: mutually recursive tuple via Bekić's theorem |

`object ParserLaws` states PEG equations (identity, associativity, zeros, choice monoid, lookahead as restriction,
double negation, loop/recursion unfolding). Note that ordered choice is *not* left-distributive, and `Strong` is only
premonoidal (effects are ordered) — tests assert these failures explicitly.

### 5.2 Mixins: combinators derived from categorical structure

Each mixin `extends ParserAlgebra`, adds a named context bound on `Self` (or `On`), and implements a slice of the
algebra **purely in terms of that structure**:

| Mixin | Requires | Implements |
| --- | --- | --- |
| `Sequencing` | `Self: Promonad on On` (`SequencingPromonad`) | `pure`, `success`, `andThen`, `map`, `mapInput` |
| `Zipping` | `Self: Strong.on[On, Empty, Pair]` (`ZippingStrong`) | `zip = first >> second` |
| `Branching` | ``Self: Cocartesian.`with`[None, Alternative]`` (`BranchingCocartesian`) | `branch`, `merge`, `or` |
| `Alternation` | `Self: Enriched over Monoid.Additive` (`AlternationEnriched`) | `failure = zero`, `orElse = +` |
| `Lookahead` | `Self: Restriction` (`LookaheadRestriction`) | `lookahead = restrict` |
| `Iteration` | ``Self: Elgot.`with`[None, Alternative]`` (`IterationElgot`) | `iterate = dagger` |
| `Recursion` | `Self: Enriched over Fixed.in[Function, Unit, LazyTuple2, Function]` (`RecursionEnriched`) | `recursive = HomIsV.fix` |
| `Concatenation` | `On: Cartesian.with[Empty, Pair]` and `Cocartesian.with[None, Alternative]` | `pair`, `skipThen`, `thenSkip`, `between`, `repeated`, `times`, `atLeast`, `separatedBy`; declares abstract `nil`, `snoc` |

`ParserAlgebra.CanonicalParser` mixes all of them. **An interpreter is "just" a choice of carrier plus overrides of
the deferred givens** — see `KleisliParser` (≈ 35 lines). When adding a combinator, prefer deriving it from existing
structure in a mixin (or as a concrete method on `ParserAlgebra`, like `optional` and `not`) over adding a new
abstract primitive.

### 5.3 `KleisliParser` and `ReferenceParser` (the specification)

- `KleisliParser`: `Self = Kleisli[StateT[Input, Try]]`, i.e. `A => Input => Try[(result: B, state: Input)]`,
  `On = Function`. All givens come from `Kleisli.*` instances. Alternation comes from
  `Kleisli.KleisliIsValuedEnriched`: `Try` is `Valued over Monoid.Additive` (`orElse`), lifted pointwise through
  `StateT` and function types — that is what yields backtracking ordered choice. Recursion comes from
  `Fixed.FunctionIsFixed` (η-expansion knot).
- `ReferenceParser extends KleisliParser`: `Input(source, offset)`, `Many = Vector`, `literal`/`regex`
  (`Matcher.lookingAt` on a region), `rule` relabels failures at the start offset, `ParseError(offset)(expected)`
  (by-name message, `NoStackTrace`). Entry points: extension `p.parse(source)` / `p.parseAll(source)` on
  `P[Unit, B]`, returning `Try[(result: B, offset: Int)]`.
- It is slow and not stack-safe on deep nesting; it is the **semantic ground truth**. Do not optimize it at the
  expense of clarity.

### 5.4 `StrictParser` (the optimizing interpreter)

`StrictParser extends CanonicalParser` with `On = Fn`, `Self = Node`. Key pieces (all in `StrictParser.scala` unless
noted):

- **`Fn`** (`Fn.scala`): reified total, pure morphisms of **Type** — `Id`, `Lift`, `Compose`, `Bang`, `Proj1/2`,
  `Fanout`, `Absurd`, `Inl/Inr`, `Copair`. Smart constructors (`andThen`, `fanout`, `copair`) normalize with
  distributive-category equations. `Fn` is a `Promonad`, `Cartesian`, `Cocartesian`. **Functions lifted with
  `Fn.lift` must be total and pure**; normalization may fuse or drop them.
- **`Node`**: sealed AST — `Rule`, `Literal`, `Scan`, `Pattern`, `Pure`, `Success`, `Failure`, `Seq`, `Zip`, `Pair`,
  `SkipThen`, `ThenSkip`, `Merge`, `Choice`, `Lookahead`, `Not`, `Loop`, `Repeat`, `Rec`. Each has
  `run(a, s: State): Out[B]`.
- **Normalizing smart constructors**, applied by the categorical instances on `Node`:
  - `sequence(p, q)` — right-associates, eliminates identities, fuses `Pure`s, turns `Δ ⨾ Zip` into `Pair`,
    `Pair ⨾ π₁/π₂` into `ThenSkip`/`SkipThen`, distributes pure post-processing into `Merge`/`Choice`.
  - `discard(node)` — strips result construction when a result is ignored (e.g. `Scan(discard = true)` avoids
    allocating the matched slice).
  - `choice(alts)` — flattens nested choices, drops `Failure`, prunes alternatives after a total one.
  - `StrictParserTest` asserts the exact normal forms (e.g. `(a && b) == Pair(Literal("a"), Literal("b"))`). If you
    change normalization, update those tests deliberately.
- **`Out[B]`**: opaque unboxed result — the value itself or a private `Failed` sentinel (`isFailed`, `get`).
- **`State`**: mutable `offset`, furthest failure (`failedAt`, `expected`) and a stack of `Head`s for left recursion.
  Errors report the **furthest** failure position.
- **`Info`**: static first-set (`CharSet`) + nullability analysis, with Kleene iteration over `Rec` knots (cached in
  `rec.info`). `Choice` uses a precomputed `Dispatch` table (128 ASCII entries + non-ASCII + end-of-input) to try only
  viable alternatives; `skipsFirst` keeps error labels identical to the reference interpreter.
- **`Rec`**: recursion knot (`lazy val body = f(this)`). If `Info.mayLeftRecurse`, uses **seed growing** to support
  direct, mutual (pairs, triples) left recursion. Consequence (tested): the fixed-point law
  `recursive(f) === f(recursive(f))` does not hold for left-recursive `f`.
- **`Repeat`**: specialized repetition with min/max/separator; stops when an iteration consumes nothing.
- **`Scanner`** (`Scanner.scala`): compiles the regex fragment of concatenated single-character atoms (literals,
  escapes, `.`, `[...]`, `\d\w\s` and negations, optional `(?s)`) with `?`, `*`, `+`, *provided every quantified atom
  is disjoint from all later atoms* (so greedy no-backtracking matching equals `java.util.regex`). Anything else →
  `Pattern` fallback (`Regex.findPrefixOf`). `ScannerTest` property-checks agreement with `Regex`.
- **`CharSet`** (`CharSet.scala`): immutable `BitSet` with inline 2×64-bit ASCII masks for fast `contains`.

Performance rules for `StrictParser.run` paths: no allocation in the hot path beyond results, no boxing (use `Out`),
`@tailrec` loops, no closures per call, avoid `Option`/tuples where a sentinel or primitive works. Re-run the JSON
benchmark before/after changes.

### 5.5 Interpreter agreement is the core invariant

`StrictParser` must behave **exactly like `ReferenceParser`** on results and consumed offsets (and failure vs.
success). This is enforced by:

- `StrictParserTest.agree(...)` — the same `Grammar[B]` (written against `ParserAlgebra.Standard` with a `lift`
  polymorphic function) run on both interpreters over a list of inputs.
- `JsonGrammarTest` — every JSON test registered for both interpreters.
- Law tests on both (`ParserLaws`, plus categorical laws on `Node` instances).

When adding or changing a combinator: (1) add/adjust it in `ParserAlgebra` (+ extension + alias if appropriate),
(2) implement it in the relevant mixin or both interpreters, (3) add a law to `ParserLaws` if one applies,
(4) test it in `ReferenceParserTest` **and** `StrictParserTest`, including an `agree(...)` grammar, (5) run `testFull`.

---

## 6. `parrot.json`

`final class JsonGrammar(tracked val algebra: ParserAlgebra.Standard)(using Lift: algebra.On is Promonad on Function)`

- Written once for any standard algebra; `lift` turns Scala functions into `algebra.On` via the promonad unit.
- Private helpers `opt` (→ `Option`) and `union` (→ union type `B | C`).
- Exposes `s`, `jsonTrue`, `jsonFalse`, `jsonNull`, `minus`, `integralPart`, `fractionalPart`, `exponentPart`,
  `number`, `unicodeEscape`, `escape`, `string`, `makeObj`, `makeArray`, `json` (recursive), `obj`, `array`.
- Result types are raw concrete syntax trees, named by aliases in the companion (`JsonNumber`, `JsonString`, …);
  `JsonJson` is a case-class wrapper that breaks the recursive alias cycle.
- Usage: `val p = new StrictParser {}; val g = JsonGrammar(p); p.parse(g.json)(input)`.
- `JsonFixtures.excluded` lists documents whose nesting overflows the stack; both interpreters are recursive-descent.

---

## 7. Coding conventions

### Formatting

- scalafmt 3.11.3 with `.scalafmt.conf` (IntelliJ preset, `maxColumn = 120`, `align.preset = more`,
  `newlines.source = keep`, trailing commas kept, `SortModifiers`). There is no sbt-scalafmt plugin; format with the
  IDE or a scalafmt CLI of that exact version, and **only touch the lines you change** (the repo is consistently
  formatted; commit "applied formatter" exists).
- Aligned `=` / `:` / `=>` columns in consecutive declarations and match cases (scalafmt `align.preset = more`).
- Braces style: method bodies are wrapped in `{ ... }` even when they are a single expression (except some trivial
  one-liners in `Fn`, `ParserAlgebra` aliases, `StrictParser`). Use Scala 3 `if … then … else`, `for … do`, and
  `match` with braces. Trailing commas in multi-line argument/parameter lists.

### Compiler-flag-driven idioms

- **`-Wnonunit-statement`**: in tests, every non-final `assert` is written `val _ = assert(...)`; the last expression
  of a test block is a bare `assert(...)`. Same for any discarded non-`Unit` value in main code (`val _ = knot.body`,
  `val _ = env.remove(rec)`).
- **`-language:strictEquality`**: `==` needs a `CanEqual`. Main code derives targeted instances
  (`given CanEqual[CharSet, CharSet] = CanEqual.derived`); parser/JSON tests use
  `given CanEqual[Any, Any] = CanEqual.derived`. Laws use `===` from `Eq`, not `==`.
- **`-Yexplicit-nulls`**: Java APIs return `T | Null`; use `.nn` (see `JsonFixtures`, `JsonBenchmark`).
- **`-Wunused:all`**: no unused imports/params/privates — remove what you don't use. Use `_` for unused lambda
  params.
- **`-Wsafe-init`**: beware of forward references in trait/class initialization; use `lazy val` where needed (e.g.
  `Rec.body`, `Choice.dispatch`).

### Documentation style

- **Every** public trait, type, given, method and law has a scaladoc comment (`/** … */`, wrapped/folded by
  scalafmt `docstrings.wrap = fold`).
- Math notation in docs: variables and objects in `*italics*`, categories in `**bold**` (`**Type**`, `**C**`,
  `**V**`), Unicode symbols (η, μ, ⊗, ⊕, π₁, ι₂, ⟨-, -⟩, [-, -], †, ∘, ⨾, Λ, Δ, ∇, ¡, !). Laws state their equation
  first, e.g. `/** *μ* ∘ (*η* ⊗ *id*) = *λ* */`.
- Type-class docs begin "A <structure> on/over …" then "Represents …, where" followed by a bulleted list of the
  structure's components. Instance docs explain the concrete structure the same way.
- Use `@note` for caveats (laws holding only up to an equivalence, required coherence conditions, etc.).
- Comments in code bodies are rare; prefer precise scaladoc.

### Naming

- Givens: `<Carrier>Is<TypeClass>`; deferred structure givens: `<Trait><Super>` (`CartesianPromonad`,
  `SequencingPromonad`); structure accessors: `SelfIs<X>`, `OnIs<X>`, `InIs<X>`.
- Law objects: `<TypeClass>Laws`, methods named after the law (`leftIdentity`, `associativity`, `fixedPoint`,
  `doubleDagger`, …).
- Extension `@targetName`s: `<method>Ext`.
- Type parameters follow the categorical docs (`A, B, C, D`, `P[_, _]`, `K[_, _]` for an underlying category,
  `U` unit, `T[_, _]` tensor, `E[_, _]` exponential).

### General

- Pure, immutable, total code in `category`. Mutation is confined to `StrictParser` run-time state, `Scanner`'s
  compiler, and benchmarks.
- Do not add library dependencies (no cats/scalaz). The point of the project is to build the structures from scratch.
- Prefer deriving behavior from existing categorical structure over ad-hoc code; if a new structure is needed, add it
  to `category` with its laws and law tests first.

---

## 8. Testing conventions

- Framework: ScalaTest `AnyFunSuite`; property checks via ScalaCheck.
- `category` tests extend **`CategorySuite`** (also used by `StrictParserTest`), which provides:
  - extensional `Eq` for `Function` and `PartialFunction` by ScalaCheck sampling (`Test.check(...).passed`),
  - "sharp" `Arbitrary` instances for `Try` (several distinct failures), `Option`, `Set`, `LazyTuple2`.
- Test names follow `"<Carrier> is <TypeClass>: <law or behavior>"` (e.g. `"Kleisli[Option] is Elgot: fixed point
  law"`, `"Function is Conway satisfies doubleDagger law"`). Sections are separated with
  `// ====…` banner comments.
- A new type class instance needs tests for **every** law in its `…Laws` object, plus behavioral examples, using
  sample morphisms that exercise interesting cases (partiality, failure, constant functions, branches).
- Parser equality in tests is extensional: equal results **and** equal offsets on sampled semantic inputs and
  sources (`ParserIsEq` in `ReferenceParserTest`, `NodeIsEq` in `StrictParserTest`).
- Negative results are tested too (e.g. "left distributivity fails", "interchange fails", "seed growing breaks the
  fixed-point law") — keep them; they document the intended semantics.
- `JsonBenchmark` is an `object` with `main` under `src/test` (not a suite). `JsonFixtures` is shared by tests and
  benchmark.

Before finishing any change: `sbt --client testFull` must pass with no new warnings. For `StrictParser`/`Scanner`/
`CharSet`/`Fn` changes, also run the JSON benchmark (at least `nativejson-benchmark`, whose JSON_checker validation
must stay 34/34) and compare throughput/allocation.

---

## 9. Git conventions

- Default branch is `main` (remote `origin`); topic branches exist for experiments (`parser`, `category`, `packrat`,
  `fix`, …). Keep history linear (rebase, no merge commits) with one logical change per commit.
- Commit subjects are **lowercase, past tense, no trailing period**, starting with a verb: `implemented X`,
  `defined X`, `added XTest`, `improved …`, `renamed …`, `eliminated …`, `fixed …`, `applied formatter`. Name types
  by their Scala identifiers (e.g. `implemented StrictParser`, `combined Pairing and Repetition to Concatenation`).
- Don't commit build outputs, IDE workspace files, or changes to vendored fixtures.

---

## 10. Quick recipes

**Add a new categorical structure `Foo`:**
1. `src/main/scala/category/Foo.scala` with `package parrot` / `package category`, a scaladoc'd `trait Foo` with
   `type Self…: Super as FooSuper`, `val SelfIsSuper`, operations + `@targetName` extensions, and `object FooLaws`.
2. Companion `object Foo` with `apply` summoner, refinement helpers if needed, and `<Carrier>IsFoo` instances using
   singleton-typed overrides.
3. `src/test/scala/category/FooTest.scala extends CategorySuite`, one test per law per instance.

**Add a new parser interpreter:** extend `ParserAlgebra.CanonicalParser`, fix the type members, override each deferred
given (`SequencingPromonad`, `ZippingStrong`, `BranchingCocartesian`, `AlternationEnriched`, `LookaheadRestriction`,
`IterationElgot`, `RecursionEnriched`, `ConcatenationOnCartesian`, `ConcatenationOnCocartesian`) and the
`OnIsCartesian`/`OnIsCocartesian` vals with singleton types, implement `rule`, `literal`, `regex`, `nil`, `snoc`, and
provide `parse`/`parseAll`. Then add it to `JsonGrammarTest` and an agreement test against `ReferenceParser`.

**Write a grammar:** take a `ParserAlgebra.Standard` (plus a way to lift functions into `On`), `import algebra.*`,
and use the combinators; use `recursive` for self-reference and `recursive[(P[…], P[…])]` for mutual recursion. Use
`rule(label)` to improve error messages. Remember `scala.None` vs the `None` type member.
