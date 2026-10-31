# CLAUDE.md — Parrot

Guidance for AI coding agents working in this repository (`AGENTS.md` points here). Read it fully before changing code: the project is small but
very dense, it leans on experimental Scala 3 features, and its conventions are strict and consistent.

---

## 1. What Parrot is

Parrot is a **parser-combinator library derived from category theory**, written in Scala 3, together with a tutorial
that explains the category theory it is derived from.

- `parrot.category` is a self-contained, dependency-free library of categorical structures (categories, functors,
  promonads, monoidal structures, strength, restriction, traces, Conway and Elgot operators, recursion, monads and their
  transformers), each with its **laws encoded as executable code**.
- `parrot.parser` defines **`ParserAlgebra`**, the combinators of parsing expression grammars, as a bundle of those
  structures: every combinator is an operation of a structure the algebra is built from. Two interpreters exist:
  - **`ReferenceParser`** — the executable *specification*: Kleisli arrows of the state transformer over the failure
    transformer over a writer of diagnostics, built entirely from library structures.
  - **`StrictParser`** — an *optimizing* interpreter that reifies parsers as an AST (`Node`) over reified pure functions
    (`Fn`), normalizes them at construction time, and runs them with mutable state and no boxing.
- `parrot.json` contains `JsonGrammar`, a JSON grammar written once against any `ParserAlgebra`, used as the main
  end-to-end test and benchmark workload.
- `docs/TUTORIAL.md` is the tutorial: the library should read as a consequence of it. Its code
  is compiled by `docs/tutorial/check-snippets.py`.

There is no `main` application, no runtime dependency, and no published artifact. The only dependencies are
ScalaTest and ScalaCheck, in `Test` scope.

---

## 2. Toolchain and build systems

| Item          | Value                                                              |
| ------------- | ------------------------------------------------------------------ |
| Scala         | `3.10.0` (`build.sbt`, `pants.toml`, `BUILD`, `check-snippets.py`) |
| Build tools   | sbt `2.0.12` (full suite, benchmarks), Pants `2.33.1` (fine-grained) |
| JDK           | developed on OpenJDK 25                                            |
| Formatter     | scalafmt `3.11.3` (`.scalafmt.conf`), no sbt plugin                |
| Plugins       | sbt: `sbt-ide-settings`; Pants: in-repo `scala_override`           |
| Test libs     | ScalaTest `3.2.20`, scalatestplus `scalacheck-1-19`                |

### Dual build system setup

Parrot maintains a **dual build system setup** where each tool serves a distinct role:

- **sbt 2** is the canonical build tool for whole-repo verification and heavy tasks: running the entire suite of ~570 law
  tests (`testFull`, which regenerates `docs/law-status.md`), executing memory-intensive benchmarks with large forked
  heaps (`Test/runMain parrot.json.JsonBenchmark`), and running the tutorial snippet checker.
- **Pants** provides fine-grained, file-level dependency tracking and isolated execution: ideal for fast developer feedback
  loops when editing, type-checking, or testing individual files or targets without paying the overhead of evaluating
  sbt's whole-project task graph.

---

### 2.1 sbt (whole-project verification and benchmarks)

* Configuration: `build.sbt`, `project/`
* Plugins: `sbt-ide-settings` (IntelliJ)

Commands (run from the repository root):

```sh
sbt --client compile                     # compile main
sbt --client Test/compile                # compile main + tests
sbt --client testFull                    # run ALL tests (about 570, under a minute) and regenerate docs/law-status.md
sbt --client test                        # sbt 2: INCREMENTAL (= testQuick) — may run nothing!
sbt --client "testOnly parrot.parser.*"
sbt --client "Test/runMain parrot.json.JsonBenchmark [--reference] [suite ...]"
python3 docs/tutorial/check-snippets.py --classpath target/out/jvm/scala-3.10.0/parrot/classes  # tutorial code, after compile
```

Important sbt 2 gotchas:

- **`test` is incremental in sbt 2** (it behaves like `testQuick`). Use **`testFull`** to know the whole suite passes.
- sbt 2 caches compilation outputs; `clean; compile` can be served from cache and complete in a couple of seconds.
- Tests and `Test/runMain` fork, with `-Xmx4g`: the reference interpreter needs more than sbt's heap on the most
  deeply nested JSON documents. `JsonFixtures` resolves `src/test/resources/json` **relative to the working directory**, so
  always run from the repository root.

Benchmark suites: `json-test-suite`, `json-dummy-data`, `json-benchmark`, `nativejson-benchmark` (all if none given).
Only `StrictParser` is measured unless `--reference` is passed. Example:
`sbt --client "Test/runMain parrot.json.JsonBenchmark nativejson-benchmark"` (≈ 110 MiB/s for `StrictParser` at the
time of writing, JSON_checker 34/34). Use it after touching `StrictParser`, `Scanner`, `CharSet` or `Fn`.

---

### 2.2 Pants (fine-grained and single-file workflows)

* Configuration: `pants.toml`, `BUILD`
* Plugins: in-repo `scala_override` (`pants-plugins/scala_override`)

Use Pants when editing or checking single files or specific targets to get fast, fine-grained feedback without
evaluating the whole project.

Commands (run from the repository root):

```sh
pants check <path-to-file>               # type-check a single file (e.g. src/main/scala/parrot/category/Strong.scala)
pants check ::                           # type-check all targets
pants test <path-to-test>                # run tests in a specific file
pants dependencies <path-to-file>        # inspect inferred dependencies for a file
```

> [!NOTE]
> Pants uses fine-grained, file-level dependency inference powered by Scalameta. Because vanilla Scalameta rejects
> Scala 3's `tracked` term parameters, Pants loads the in-repo plugin `scala_override` (`pants-plugins/scala_override`)
> to patch `ScalaParser.scala` with `dialects.Scala3Future`. It also reads `?->` as `?=>`, because Scalameta rejects the
> pure arrows that capture checking requires in polymorphic function types (§11).
>
> In `Closed.scala`, the infix exponential type operator is escaped as `` `^` `` to prevent collision with Scalameta's
> capture-checking syntax.

---

### 2.3 Compiler flags (from `build.sbt` and `pants.toml`)

| Flag | Purpose / Note |
| ---- | -------------- |
| `-source:future` | Future Scala language behavior and syntax |
| `-preview` | Preview compiler features |
| `-language:experimental.modularity` | Modularity features: `A is TC`, `type Self`, and `tracked` parameters |
| `-language:experimental.pureFunctions` | Pure function types: `A -> B` |
| `-language:experimental.captureChecking` | Capability and capture checking: `->` is checked in the library and tests |
| `-language:experimental.genericNumberLiterals` | Generic numeric literal syntax |
| `-language:experimental.saferExceptions` | Tracked exceptions using `canThrow` capabilities |
| `-language:strictEquality` | Multiversal equality: `==` requires `CanEqual` instances |
| `-Yexplicit-nulls` | Explicit nullability; Java interop returns `T \| Null` |
| `-Wunused:privates,locals,params,patvars` | Report unused private members, locals, parameters, and pattern variables |
| `-Wvalue-discard` | Warn when a non-`Unit` expression result is discarded |
| `-Wnonunit-statement` | Warn when statements do not have `Unit` type (`val _ = assert(...)` in tests) |
| `-deprecation` | Emit warning and location for usages of deprecated APIs |
| `-feature` | Emit warning and location for features requiring explicit import |
| `-unchecked` | Enable additional warnings where generated code depends on assumptions |
| `-explain` | Explain errors in more detail |
| `-explain-types` | Explain type errors in more detail |

> [!NOTE]
> `-Wsafe-init` and `-Wunused:imports` are deliberately disabled in both `build.sbt` and `pants.toml` due to compiler false positives:
> - `-Wsafe-init`: False positives when a `tracked` constructor parameter is forwarded to a parent class (see §4.1 Rule 11 and `docs/DESIGN.md` §10).
> - `-Wunused:imports`: False positives on renamed type imports like `import D.--> as ==>` (see §4.1 Rule 14 and `docs/DESIGN.md` §10).

Tests are compiled **with** capture checking too. ScalaCheck is not capture-checked, so its generated functions are
trusted to be pure. **Keep the build warning-free.**

---

## 3. Repository layout

```
build.sbt, project/                sbt 2 build
pants.toml, BUILD, pants-plugins/  Pants 2.33.1 build and scala_override plugin
.scalafmt.conf                     scalafmt 3.11.3, dialect scala3Future, maxColumn 120
src/main/scala/parrot/
  category/   (package parrot.category)   the categorical library
  parser/     (package parrot.parser)     ParserAlgebra, Expected, the two interpreters, Fn, Scanner, CharSet
  json/       (package parrot.json)       JsonGrammar
src/test/scala/parrot/
  category/   LawSuite (law runner + law status table), Sample, CategoryFixture, PromonadFixture (generators,
              observations), one spec per structure
  parser/     Grammars (random grammars), law and agreement tests, interpreter tests, ScannerTest
  json/       JsonGrammarTest, JsonCorporaTest (every corpus document), JsonFixtures, JsonBenchmark (a `main`)
src/test/resources/json/           vendored JSON corpora (see README.txt there for upstream sources/commits)
docs/
  TUTORIAL.md                      the tutorial, "Practical Programming with Categories"
  DESIGN.md                        the design rationale: decisions, rejected alternatives, removed constructs, open issues
  law-status.md                    GENERATED by every test run: law × instance × status
  tutorial/                        the snippet checker for the tutorial
```

Sources live in `src/{main,test}/scala/parrot/<pkg>/` and declare chained package clauses:

```scala
package parrot
package category
```

Always use this two-clause header in new files. Never commit `target/`, `.bsp/`, or `.idea`. Don't edit the vendored
JSON fixtures.

---

## 4. Architecture: `parrot.category`

### 4.1 The encoding (read this first)

The rationale is in `docs/DESIGN.md` §3; the rules:

1. **Abstract classes for structures, traits for plain type classes.** Every categorical structure is an `abstract
   class … extends caps.Pure` (structure must be pure): traits cannot pass constructor arguments to parents, and
   refinement chains need them. Type classes without parameters that are not categorical structures (`Type`, `Eq`,
   `Observable`, `Preorder`, `Measure`) are traits.
2. **Bases are `tracked` term parameters.** A structure on something else takes it as a parameter:
   `abstract class Bistrong(tracked val P: Profunctor { val V: Total.type; val K2: K1.type }, tracked val M: Symmetric { val K: P.K1.type })`.
   A parameter is a stable path, so `P.K1.Obj`, `M.Tensor`, `import M.given` work, and `tracked` keeps its singleton type
   in the instance's type: no casts, no `ValueOf`. A constraint between parameters refines the *later* one towards the
   earlier (`M { val K: P.K1.type }`), never the other way (§11).
3. **`Self` iff the structure has its own carrier** (`Category`, `Bifunctor`, `Functor`, `Profunctor`, `Promonad`,
   `Monoid`, `Comonoid`, `Eq`, `Observable`). Structures *on* something else (`Monoidal`, `Module`, `Strong`,
   `Restriction`, `Traced`, `Conway`, `Elgot`, `Recursion`, and `Monad`, which is structure on an `Endofunctor`) have no
   `Self` and are named, not found by carrier: one category carries several (products and coproducts).
4. **Refinements forward their parameter under the same name**: `abstract class Promonad(tracked override val K:
   Category) extends Endoprofunctor(K, Total)`.
5. **Combinations are bundles**, not inheritance: `ParserAlgebra(…)` takes all the parser's structures as `tracked`
   parameters and derives or `export`s their operations. A structure that is another with more operations extends it
   instead: `Freyd(P, S)` is the category of arrows `Promonad.Arrows(P)` with a strength `S`.
6. **Object evidence**: a category's objects are the types with evidence `type Obj <: Type`. `Type` holds for every
   type (`Type.TIsType`); refinements such as `Eq` select fewer. Evidence is passed only through context bounds,
   except evidence that chooses an object, which is a `tracked` parameter: the unit `U` of `Monoidal(K, U, T)`, whose
   type is the unit object `I = U.Self`.
7. **Instances are `object`s** with descriptive names, nested in what they belong to: `Total.Product`,
   `Total.Coproduct`, `Total.Exponential`, `Partial.Loops`, `Kleisli.OptionKleisli`. Generic constructions are `open
   class`es (`Kleisli(M)`, `StateT[S](M)`, `Kleisli.ClassicalOf(P, R)`), instantiated by objects.
8. **Instances name their evidence explicitly** (`Type.TIsType`), never `summon`: a class-level forwarding given would be
   found and recurse.
9. **One operator name per operation**: `>>>`/`<<<` (composition in a category and in a promonad, diagrammatic and
   mathematical order), `***` (tensor), `&&&`/`|||` (pairing, copairing), `+++` (coproduct tensor), `**` (Freyd
   parallel), `|>` (override), `=?=` (observable agreement), `?<` (preorder), `===` (Eq). Same-named extensions from two
   imports form an overload resolved by the receiver's type, so `import S.P.K.>>>` and `import S.P.{P, >>>}` coexist.
   **Exception:** where a promonad's arrow is also an arrow of its base, both apply to one value: a Kleisli promonad on
   𝒮 (`A -> M[B]`) and a hom promonad. Scala then reports an ambiguity or picks one and rejects the argument, never a
   wrong composition; such code imports one `>>>` and names the other (`M.K.andThen(f, M.bind(g))` in `Kleisli`).
   A promonad and its category of arrows (`P.category`, `Freyd`) share their arrows and compose them alike, but
   importing both `>>>` is ambiguous: import one.
   **Operators are syntax:** every symbolic extension passes its arguments one-to-one, in order, to a named method of
   the same structure, which holds the logic and the name (`f >>> g` is `andThen(f, g)`, `q <<< p` is `compose(q, p)`,
   `p ** q` is `parallel(p, q)`, `~p` is `lookahead(p)`). An operator computes nothing of its own; its doc is `Infix
   extension for [[andThen]].`
10. **Nullary extensions that clash with a method of the same name** take `(using DummyImplicit)`.
11. **`-Wsafe-init` is off** (commented out in `build.sbt`): a *class* that forwards a `tracked` parameter to a parent
    class with parameters gets a false "Access non-initialized value" (objects are fine; the scala3 issue draft is
    `docs/DESIGN.md` §10), and so does every test class that extends a spec passing such a parameter to `LawSuite`.
    Do not add `@nowarn` for it. In test specs, still prefer `lazy val` for members computed from parameters.
12. **No given with `Self = Nothing`**: Scala 3.10.0 finds it for every `T is TC` query. `Eq.NothingIsEq` is a plain
    `val` for that reason.
13. **Name the carrier** with a public `final` alias: `Hom` (and infix `-->`) for a category, `F` for a (bi/endo)functor,
    `P` for a profunctor or promonad, `M` for a monoid (and, as `M = F.F`, for a monad), `C` for a comonoid.
    Object-level infix aliases: `*` (tensor), `+` (coproduct), `` `^` `` (`Closed.Exp` in the order of the exponential *B*ᴬ: `B `^` A` = *A* ⇒ *B*, backticked for Scalameta capture checking compatibility), `<->`
    (`Category.Iso`, `A <-> B`).
14. **Arrows, not `.Self`.** Write morphisms infix: `-->` for the category at hand, `->>` for a second category (a
    functor's target, a bifunctor's second source), `==>` for a target category (bifunctor, profunctor) or the base of a
    category of arrows (`Freyd`), `~~>` for an opposite category. These three-symbol arrows name roles; the two concrete
    categories have two-symbol arrows, `A -> B` in `Total` and `A ~> B` in `Partial` (`type ~> = Partial`, used inside
    `object Partial` too). Bring the role arrows and `Obj` into scope with **imports** (`import K.{Obj, -->, >>>}`,
    `import S.P.{P, >>>}`, `import S.P.K.{Obj, -->}`), renaming where categories meet (`import D.--> as ==>`), never
    with new type definitions. Renamed type imports trigger a false `-Wunused` warning, which is why `-Wunused:imports`
    is commented out in `build.sbt` and `pants.toml`. Parenthesize: `+`, `-->` and `->>` share a precedence level, so
    write `(A + B) --> C`; `*` binds tighter, `<->`, `==>` and `^` looser, `~>` and `~~>` tighter than `*`. Parenthesize
    arrows next to `->` and `is` as well: `(A ~> B) -> (A ~> B)`, `(X ~> Y) is Observable`.
15. **Eta-reduce aliases** whose parameters are only passed on: `final type * = Tensor`, `type Self = Tuple2`.
16. **`final`** on what is definitional: aliases and extension methods that only forward (`>>>`, `***`, `|>`, `first`,
    `restricted`, the parser syntax); **`override` without `final`** when redefining an inherited member. A member that
    only forwards to a member of a parameter, with the same type parameters, is an **`export`**, not a new `def`
    (`Monad` exports `K`, `M`, `map`, `objects` from its functor; `ParserAlgebra` exports `pure`, `success`, `failure`,
    `lookahead`, `not`, `attempt`, `optional`, `orElse` from its structures). Exports are final. An export that gives
    members a new meaning carries one scaladoc on the clause, saying what the new names mean (`ParserAlgebra`:
    `unit as pure`, `complement as not`); one that only forwards needs none, since the members keep their own docs
    (`Monad`, which only names its carrier `M`, as rule 13 does).
17. **Monads have their functor**: `abstract class Monad(tracked val F: Endofunctor)` with primitives `unit` and
    `flatten`; `map`, `objects` are exported from `F`, `bind` is derived. Refine monads through the functor, `Monad.On[Total.type]` =
    `Monad { val F: Endofunctor { val K: Total.type } }`, not `Monad { val K: Total.type }`: only the former keeps the
    chain of singleton types (`M.K` = `M.F.K` = `Total`) that lets `Strong.Bistrong(P, Total.Product)` type-check.
    Transformers define their endofunctor in their companion (`Writer.FunctorOf`, `OptionT.FunctorOf`,
    `StateT.FunctorOf`).

### 4.2 Two categories of programs

- **`Total`** is 𝒮: total, pure functions `A -> B`. Totality is a promise.
- **`Partial`** is 𝒫: `opaque type Partial[A, B] = A -> B`, written `A ~> B`, programs that may diverge.
  `Partial(f)` is a program, total or not; `Partial.fromTotal(f)` includes a morphism of 𝒮 (use it where `f` is
  total); **`Partial.assumeTotal(p)` is the single totality promise** of the library. 𝒫 has the unguarded structures:
  restriction (`Domains`), while loops (`Loops`), feedback (`Feedback`), recursion at function types (`Knots`).
- Iteration and recursion that must be total are **guarded** by a `Measure` on the state: `StateT.GuardedIteration`,
  `StateT.GuardedRecursion` fail (with the restriction zero) on a step or call that makes no progress.

### 4.3 Catalogue

| File | Structure | Key members | Instances |
| --- | --- | --- | --- |
| `Type`, `Eq` | object evidence; semantic equality on data | `equal`, `===`, `EqLaws`, `structural` | primitives via `structural`; `Option`, `Either`, tuples and `Seq`s componentwise |
| `Observable`, `Preorder` | law-checking oracles for = and ⊑ | `agree`/`=?=`, `below`/`?<`, `through`, `function`, `ObservableLaws`, `PreorderLaws` | data via `Eq`; pairs componentwise (in the parent `ComponentwiseObservable`); `Preorder.of` a semilattice |
| `Category` | category with object evidence | `Hom`/`-->`, `identity`, `compose`/`<<<`, `andThen`/`>>>`, `Iso`/`<->`, `op`, `CategoryLaws`, `IsoLaws` | `Total`, `Partial`, `Fns`, `Category.Op`, `Category.Product` (pair types, taken apart by the match types `Fst`, `Snd`) |
| `Functor` (+ `Endofunctor`), `Bifunctor`, `Profunctor` (+ `Endoprofunctor`) | (bi/pro/endo)functors between given categories; a bifunctor is a functor out of the product via the view `functor` (`Bifunctor.FromProduct`), whose functor laws are its laws | `F`, `map`, `bimap`, `dimap`, `functor`, `op` | `Endofunctor.OptionIsEndofunctor`, `Partial.Inclusion` (𝒮 → 𝒫), `Total.Tuple2IsBifunctor`, `Bifunctor.Op`, … |
| `Promonad` | monoid in endoprofunctors: a category of arrows over **K** | `unit`, `multiply`, `identity`, `compose`/`<<<`, `andThen`/`>>>`, `category` (`Arrows`), `Op`, `Hom` | `Kleisli(M)`, `Total.Functions`, `Partial.Programs` |
| `Monoidal` (+ `Module`), `Symmetric`, `Cartesian`, `Cocartesian`, `Closed` | monoidal structure and actions on a category | `***`, `act`/`~~`, unitors, `braid`, `fst`/`snd`/`&&&`, `inl`/`inr`/`|||`, `curry`, `internalHom` | `Total.Product`/`Coproduct`/`Exponential`, `Module.OfMonoidal`, `Partial.Product`/`Coproduct`, `Cartesian.Op`/`op`, `Cocartesian.Op`/`op` |
| `Strong` (+ `Strong.Bistrong`), `Freyd` | strength on a profunctor over left modules (a Tambara module); bistrong: over a symmetric structure acting on itself, with a right strength; Freyd: the category of arrows of a promonad with a bistrong structure | `left` (*τ*), `right` (*τ*′), `compatibility`; Freyd's `first` = `right`, `second` = `left`, `parallel`/`**` | `Kleisli.ProductStrength`/`CoproductStrength`, `Strong.Bistrong.Hom`, `Strong.Bistrong.Op` |
| `Restriction`, `Classical` | restriction category; zero, complement, override, attempt | `restrict`, `zero`, `complement`, `orElse`/`|>`, `attempt` | `Partial.Domains`, `Kleisli.RestrictionOf`/`ClassicalOf` |
| `Traced`, `Conway`, `Elgot`, `Recursion` | the trace/fixed-point grid; recursion at arrow types | `trace`, `fix`, `iterate` | `Partial.Loops`/`Feedback`/`Knots`, bridges `OfElgot`/`OfConway`/`OfTraced`, guarded state |
| `Monoid`, `Semilattice`, `Comonoid` | monoid and comonoid objects in a monoidal **V** | `M`/`C`, `unit`, `multiply`, `counit`, `comultiply` | tests; `parser.Expected.Furthest`; `Cartesian.comonoid`, `Partial.Product.comonoid` |
| `Monad`, `Kleisli`, `Writer`, `OptionT`, `StateT` | monads on an endofunctor; the Kleisli promonad; transformers | `unit`, `flatten`; derived `map`, `bind` | `Monad.OptionIsMonad`, `Kleisli.OptionKleisli` |
| `RestrictionMonad`, `ClassicalMonad`, `ElgotMonad`, `Measure` | monad-level presentations whose laws are the Kleisli ones | `restrict`, `orElse`, `attempt`, `iterate` | `ClassicalMonad.OptionIsClassical`, `StateT.ClassicalOf`, `OptionT.ClassicalOf` |

### 4.4 Laws

Every structure has a nested `object <Name>Laws` whose methods return `Boolean`. **Laws compare with an `Observable`**
(`(using X is Observable)`, infix `=?=`) — a finite set of observations ending in data compared with `Eq` — never with
`Eq` on functions. Inequations take a `Preorder` (`?<`). **Congruence laws** take variants equal by construction
(`f2`), because agreement on samples is not a congruence. Conditional laws (uniformity, guardedness) state their premise
in a `@note` and are tested with targeted generators. The oracles have laws too: an `Observable` is an equivalence and
**sound** (variants agree), a `Preorder` is a preorder, sound, and contains agreement (*a* =?= *b* implies *a* ⊑ *b*,
for an `Observable` at the same sample points, such as `ParserGen.oracles`).

---

## 5. Architecture: `parrot.parser`

### 5.1 `ParserAlgebra`

`abstract class ParserAlgebra(Arrows, Products, Coproducts, Zipping, Branching, Choice, Loops, Knots)`: a parser
`P[A, B]` consumes a prefix of the input while turning a semantic input `A` into a result `B`. `-->` is the category of
pure functions (`Fn` or `->`), `lift` includes a Scala function into it. Semantic types are fixed: `Unit`, `Tuple2`,
`Either`, `Nothing`, `Vector`.

| Combinators | Structure |
| --- | --- |
| `pure`, `success`, `>>`, `map`, `mapInput` | `Arrows`: a promonad over `-->` |
| `**` (`zip`), `&&`, `*>`, `<*`, `between` | `Zipping`: strength over products (a Freyd category); concatenation uses `Products` |
| `++` (`branch`), `\|\|` (`merge`) | `Branching`: strength over coproducts |
| `failure`, `~` (lookahead), `!` (not), `attempt`/`optional`, `\|>` (`orElse`), `+>` (`or`) | `Choice`: classical restriction structure; `\|>` is override (PEG ordered choice) |
| `iterate`, `repeated`, `times`, `atLeast`, `separatedBy` | `Loops`: **guarded** iteration — a step that continues without consuming input fails |
| `recursive`, `recursive[T <: Tuple]` (mutual) | `Knots`: **guarded** recursion — a recursive call without progress fails; tuples use `fixFamily`, one knot per parser |

Primitives each interpreter implements: `lift`, `literal`, `regex`, `rule`, `diagnose`. `run`, `parse`, `parseAll` are
derived (`StrictParser` overrides `run` and `parse` with a fast path).

**Diagnostics** (`Expected.scala`): a parse reports `Expected(position, expectations)`, the furthest position where
something failed and what was expected there, each `Expectation(label, context)` carrying the names of the enclosing
rules. It is a join-semilattice (`Expected.Furthest`) produced as a writer effect on success and failure. Lookahead,
negation, `failure` and guard failures are **silent** (⊥). `rule(p, l)` reports `l` where `p` fails at or before its
start, and otherwise pushes `l` onto the context of `p`'s expectations.

`ParserLaws` has two tiers: equations (results, offsets and diagnostics, with an `Observable`) and inequations ⊑ (same
results, at least as much diagnostics, with a `Preorder`): right zero, **R1** and **R4** are inequations because silent
lookahead forgets diagnostics. Keeping the diagnostics of tests instead (`OptionT.ClassicalOf`) would make R1 and R4
exact but break R2 and the zero and complement laws (tested in `RestrictionTest`), so silent is the better choice.
Monotonicity laws say every combinator preserves ⊑ (enrichment over preorders).

### 5.2 `ReferenceParser`

`P[A, B] = A -> Input -> (Expected, Option[(B, Input)])`: `Kleisli(StateT[Input](OptionT(Writer(Expected.Furthest))))`
with the classical structure `ReferenceParser.Silent` (silent tests) lifted through the state, and guarded iteration
and recursion measured by the remaining input. Slow, not stack-safe on deep nesting: the **semantic ground truth**. Do
not optimize it at the expense of clarity.

### 5.3 `StrictParser`

`StrictParser` with structures in its companion (`Nodes`, `Zipping`, `Branching`, `Backtracking`, `Loops`, `Knots`)
over `Fns` (the category of `Fn`). Key pieces (all in `StrictParser.scala` unless noted):

- **`Fn`** (`Fn.scala`): reified total, pure morphisms (`Id`, `Lift`, `Compose`, `Bang`, `Proj1/2`, `Fanout`, `Absurd`,
  `Inl/Inr`, `Copair`) with normalizing smart constructors; `Fns` is their category with reified `Product` and
  `Coproduct`. **Functions lifted with `Fn.lift` must be total and pure.**
- **`Node`**: sealed AST — `Rule`, `Literal`, `Scan`, `Pattern`, `Pure`, `Success`, `Failure`, `Seq`, `Zip`, `Pair`,
  `SkipThen`, `ThenSkip`, `Merge`, `Choice`, `Lookahead`, `Not`, `Loop`, `Repeat`, `Rec`.
- **Normalization** (`sequence`, `discard`, `choice`): the derived combinators collapse into dedicated nodes
  (`a && b == Pair(…)`, `a || b == Merge(…)`); `StrictParserTest` asserts the normal forms.
- **`State`** has a `diagnostics` flag. Without it nothing is recorded and `Choice` dispatches on the next character
  through a precomputed table from **`Info`** (first set and nullability; invariant: if a parser succeeds where the next
  character is `c`, then `c ∈ first`, or it is `nullable` and consumed nothing). With it, every alternative runs and
  failures are recorded exactly as the reference does. `parse` runs fast and re-runs with diagnostics only on failure.
- **`Rec`**: recursion knot; a re-entrant call at the same position fails (guarded), except with the same semantic
  input, which is left recursion, solved by **seed growing** — an extension beyond the reference.
- **`Repeat`**, **`Loop`**: guarded; `Repeat` avoids allocating a builder for zero or one item.
- **`Scanner`**, **`CharSet`**: compiled regex fragment and fast character sets (unchanged by the redesign).

Performance rules for `run` paths: no allocation beyond results, no boxing (`Out`), `@tailrec` loops, no closures per
call. Re-run the JSON benchmark before/after changes.

### 5.4 Interpreter agreement is the core invariant

`StrictParser` must behave **exactly like `ReferenceParser`** — results, offsets **and diagnostics** — on every grammar
without left recursion. `AgreementTest` checks it on random grammars (`Grammars.terms`, an interpreter-independent
grammar language), `JsonGrammarTest` and `JsonCorporaTest` on JSON, and both interpreters run the same law specs.

When adding a combinator: (1) derive it in `ParserAlgebra` from a structure if possible, (2) add a `Grammars.Term` case
if it changes what grammars can express, (3) add laws to `ParserLaws`, (4) test both interpreters, (5) run `testFull`.

---

## 6. `parrot.json`

`final class JsonGrammar(tracked val algebra: ParserAlgebra)`: written once for any algebra; `algebra.lift` turns Scala
functions into pure functions. Usage: `val p = StrictParser(); val g = JsonGrammar(p); p.parse(g.json)(input)`.
Documents are parsed on a thread with a 1 GiB stack (`JsonFixtures.onDeepStack`), so what the parsers accept does not
depend on the JVM's stack size; `JsonCorporaTest` asserts every corpus document on both interpreters.

---

## 7. Coding conventions

### Formatting

- scalafmt 3.11.3 with `.scalafmt.conf`. There is no CLI on the path; format with the IDE, or with a scalafmt-core
  driver, and **only touch the lines you change**. scalafmt cannot yet parse some given syntax (`given X: [A: Eq] => …
  is Eq {`, anonymous `given (… is Observable) = …`); those files are formatted by hand.
- Aligned `=` / `:` / `=>` columns in consecutive declarations and match cases.
- Method bodies are wrapped in `{ ... }`. Scala 3 `if … then … else`, `for … do`, `match` with braces. Trailing
  commas in multi-line argument/parameter lists.
- Braces in imports only around several selectors: `import K.-->`, `import D.--> as ==>`, but `import K.{Obj, -->}`.

### Compiler-flag-driven idioms

- **Capture checking** (main and tests): write function types as `A -> B`; structure classes and test fixtures extend
  `caps.Pure`.
- **`-Wnonunit-statement`**: in tests, every non-final `assert` is written `val _ = assert(...)`.
- **`-language:strictEquality`**: `==` needs a `CanEqual`. Laws use `=?=`/`===`, not `==`.
- **`-Yexplicit-nulls`**: Java APIs return `T | Null`; use `.nn`.
- **`-Wunused`**: `-Wunused:privates,locals,params,patvars` is enabled; `imports` is off (rule 14 of §4.1).
- **`-Wsafe-init`** is off (rule 11 of §4.1); still use `lazy val` for forward references.

### Documentation style

- **Every** public class, type, given, method and law has a scaladoc comment; exports only when they give members a
  new meaning (rule 16 of §4.1).
- Math notation in docs: variables in `*italics*`, categories in `**bold**` (`**K**`, `**V**`) or as 𝒮 and 𝒫, Unicode
  symbols (η, μ, ⊗, ⊕, π₁, ι₂, ⟨-,-⟩, [-,-], †, ∘, ⨾, ⊳, ⊑, ⊔).
- **Math mode composition** uses `∘` (or `⨾` where diagrammatic order reads better); **no spaces in math argument
  lists**: `**C**(*A*,*B*)`, `⟨*f*,*g*⟩`.
- Laws state their equation first, e.g. `/** *μ* ∘ (*η* ⊗ *id*) = *λ* */`.
- Infix names have one-line docs: `Infix alias for [[Hom]].` on a type alias, `Infix extension for [[compose]].` on
  an extension method.
- Structure docs begin "A <structure> on …" then "Represents …, where" followed by a bulleted list of components.
- Use `@note` for caveats (unchecked premises, laws holding only for guarded arguments).

### Composition and code style

- **No unicode in Scala code**: use `*`, `+`, `-->`, `>>>`; unicode is for docstrings.
- Code uses diagrammatic composition (`>>>`); math in docs uses `∘`.

### Naming

- Instances: descriptive `object`s nested in what they belong to (`Total.Product`, `Partial.Loops`,
  `Kleisli.OptionDomains`); givens `<Carrier>Is<TypeClass>` (`OptionIsEq`, `InputIsMeasure`).
- Law objects: `<Structure>Laws`, methods named after the law (`leftIdentity`, `fixedPoint`, `overrideAssociativity`).
- Extension `@targetName`s: `<method>Ext`.
- Structure parameters are capitalized (`K`, `P`, `M`, `S`, `E`); type parameters follow the docs (`A, B, C, X, U`).

### General

- Pure, immutable, total code in `category`. Mutation is confined to `StrictParser` run-time state, `Scanner`'s
  compiler, test infrastructure, and benchmarks.
- Do not add library dependencies. The point of the project is to build the structures from scratch.
- Prefer deriving behavior from existing structure; a new structure goes into `category` with its laws, a spec and at
  least one instance first.

---

## 8. Testing conventions

- Framework: ScalaTest `AnyFunSuite`; properties via ScalaCheck generators run by **`LawSuite(structure, instance)`**
  (`law(name) { ... }`, `counterexample(name) { ... }`, `forAll(...)`), which records every outcome in
  **`docs/law-status.md`** (regenerated after each run; do not edit it by hand). The suite provides the subject of its
  laws as a given; laws of another structure the instance has go in a block, `also("Category") { law(...) { ... } }`.
- **Sample types**: specs are generic in the types they check their laws at: *T1*, …, *T4* of a `SampleTypes` bundle,
  a context parameter (`using types: SampleTypes`, then `import types.{T1, T2, given}`). In a using clause, the
  fixture comes first, `types` and then the spec's samples come last (`sample`, `tensor`, `unit`), resolved where the
  test class is declared from polymorphic givens such as `Sample.Tuple2Samples`, so that test classes need no sampling
  code. The default given `SampleTypes.Standard` is `Int`, `String`, `Boolean`, `Long`, four distinct types, so call
  sites name no types. Types that a generator forces stay concrete: the `Int` states of loops and recursion, the
  parser's `Int` semantics.
- **Law bodies**: a spec imports its fixture (`import category.*`, `import promonad.*`), its carrier where it has one
  (`import M.M`), and its laws (`import M.MonadLaws.*`; those of an `also` structure inside its block), and each law
  binds its generators to local vals named after what they sample, `observations` for the observer and the plural of
  the lambda parameter otherwise: `val fs = arrow[T1, T2]`, then, after a blank line,
  `forAll(observations, fs, gs) { (observe, f, g) => ... }`.
- **Instance names from types**: a spec whose instance is named after a type takes a `TypeName[T]` named `typename`
  (a macro, resolved where the test class is declared), so that callers pass only types:
  `class IntIsEqTest extends EqSpec[Int]`, `BifunctorSpec(Total, Total.Tuple2IsBifunctor)` is "Tuple2 on Total".
- **One generic spec per structure** (`EqSpec`, `ObservableSpec`, `PreorderSpec`, `CategorySpec`, `FunctorSpec`,
  `BifunctorSpec`, `PromonadSpec`, `MonoidalSpec`, `SymmetricSpec`, `CartesianSpec`, `CocartesianSpec`, `ModuleSpec`,
  `StrongSpec`, `FreydSpec`, `RestrictionSpec`, `ClassicalSpec`, `ElgotSpec`, `ConwaySpec`, `TracedSpec`,
  `RecursionSpec`, `MonadSpec`, `MonoidSpec`, `SemilatticeSpec`, `ComonoidSpec`, `ParserLawSpec`), **one class per
  instance**.
- **Fixtures** (`Sample.scala`, `CategoryFixture.scala`, `PromonadFixture.scala`): `Sample[X]` (generator,
  cogenerator, `Eq`; a carrier without an `Eq` is sampled at an instance where it is data, as `StateT` at `Boolean`
  states), `CategoryFixture` (arrows of a category whose objects are all types: `arrow`, `variant`, `observe`),
  `PromonadFixture` (arrows of a promonad, with a `base` fixture for pure arrows). Observations generate **fresh
  sample points per property**.
- **Specs take their subject, not a fixture**: the category or structure is a `tracked` parameter whose type states
  what the laws need (`tracked val M: Symmetric { val K: Category { type Obj = Type } }`), and the fixture is found
  from it as a given, `using category: CategoryFixture.On[M.K.type]` (`promonad: PromonadFixture.On[S.P.type]` for
  promonads), a `val` only where a test class uses it. The fixture's name names the category in test names, so a spec
  needs no `TypeName` of its category.
  There is one given fixture per category or promonad, in the companions `CategoryFixture` and `PromonadFixture` (the
  parser's in `ParserFixtures`, imported). Derived categories (`Total.op`, `P.category`) need givens of their own:
  implicit search cannot get from `Total.op` back to `Total`. `FunctorSpec` finds two fixtures, `source` for the
  arrows it maps and `target` for the observations. `ObservableSpec` alone takes its fixture explicitly, since the
  fixture's observer is what it tests.
- Conditional laws use targeted generators (`Descent` for loops that stop, `StringStateFixture.guarded` for guarded
  steps, `refined` pairs for monotonicity), not `==>`.
- Negative results are **counterexample** tests (interchange fails for parsers, postcomposition does not distribute
  over `|>`, guarded fixed points fail for left recursion, R1 fails exactly with silent lookahead): keep them, they
  document the intended semantics.
- Test names: `"<Instance> is <Structure>: <law>"`.

Before finishing any change: `sbt --client testFull` must pass with no warnings. For `StrictParser`/`Scanner`/`CharSet`/
`Fn` changes, also run the JSON benchmark (at least `nativejson-benchmark`, JSON_checker 34/34). For tutorial changes,
and for library changes that the tutorial uses, run the snippet checker (§2).

---

## 9. Git conventions

- Default branch is `main` (remote `origin`). Keep history linear (rebase, no merge commits) with one logical change per
  commit. The tag `pre-prune` marks the last commit before the redesign's pruning.
- Commit subjects are **lowercase, past tense, no trailing period**, starting with a verb: `implemented X`,
  `defined X`, `added XTest`, `improved …`, `renamed …`, `eliminated …`, `fixed …`, `applied formatter`.
- Don't commit build outputs, IDE workspace files, or changes to vendored fixtures.

---

## 10. Quick recipes

**Add a new categorical structure `Foo`:**
1. `src/main/scala/parrot/category/Foo.scala`: a scaladoc'd `abstract class Foo(tracked val …) extends caps.Pure` (or a
   refinement forwarding its parameters), its operations with infix extensions, and `object FooLaws`.
2. Instances as `object`s (concrete) or `open class`es (generic) in the companion or next to their carrier.
3. `src/test/scala/parrot/category/FooTest.scala`: an abstract `FooSpec(structure)(using fixture, …)` with one
   `law(...)` per law, and one test class per instance; a new category or promonad also needs a given fixture.

**Add a new parser interpreter:** choose the structures (a promonad over a category with `Obj = Type`, products and
coproducts with `Unit`/`Tuple2` and `Nothing`/`Either`, the two strengths, a classical structure, guarded iteration and
recursion), extend `ParserAlgebra(…)`, implement `lift`, `literal`, `regex`, `rule`, `diagnose`. Add it to
`Interpreters`, the law and structure specs, `AgreementTest` and `JsonGrammarTest`.

**Write a grammar:** take a `ParserAlgebra`, `import algebra.*`, use the combinators and `lift` for pure functions; use
`recursive` for self-reference (calls must come after consumed input) and `recursive[(P[…], P[…])]` for mutual
recursion; use `rule(label)` for diagnostics.

---

## 11. Implementation lessons

Things that cost time once; check here before fighting the compiler.

- **Singleton chains.** Path-dependent code type-checks when every link is declared with a singleton type (`P.K` =
  `M.K` = `M.F.K` = `Total`). A refinement that intersects instead (`Monad { val K: Total.type }` on a member already
  typed `F.K.type`) breaks the chain; refine the parameter the member comes from (`Monad.On`).
- **Chains run from the later parameter to the earlier.** `Bistrong(P { val K2: K1.type }, M { val K: P.K1.type })`
  works; `Bistrong(M, P { val K1: M.K.type; val K2: M.K.type })` does not: for a promonad, `P.K1` then points both to
  `M.K` and to the promonad's own `P.K`, and nothing makes those two equal, so `Freyd`, `Conway` and `Elgot` lose
  `Obj` and the `Op` instances become cyclic. Intersections (`M { val K: P.K1.type & P.K2.type }`) are not needed.
- **Overloaded operators across structures.** `import P.K.>>>` and `import P.{P, >>>}` merge into an overload, resolved
  by the receiver's type, and extensions are also found in the implicit scope of a path-dependent type's prefix (`K.Hom`
  finds `K.>>>` without an import). On a Kleisli promonad on 𝒮 both apply: concretely (`String -> Option[Int]`) the call
  is ambiguous, and in code generic over `Kleisli { val M: Monad.On[Total.type] }` it resolves to `Total`'s `>>>` and
  rejects the argument; inside `Kleisli` itself, `f >>> M.bind(g)` resolved to the promonad's. Both readings type-check
  only if *B* = *M*(*B*), so the result is a compile error, never a wrong composition (rule 9). Settled by a spike in
  October 2026.
- **Anonymous classes lose the parent's tracked refinement.** Inside `new Bistrong(Promonad.Op(S.P), …) { … }` the
  body sees `P` only at its declared type, not as `Promonad.Op(S.P)`; a named class (`Bistrong.Op`) keeps it.
- **A refinement cannot name a parameter that its members shadow.** In `Freyd(P, S: Bistrong { val P: P.type })`, the
  `P` inside the braces is the refinement's own member (a cyclic reference), and `Freyd.this` is not available in a
  constructor. Refine through an alias declared elsewhere, as `Monad.On` does: `S: Strong.Bistrong.On[P.type]`.
- **Renamed type imports** (`import D.--> as ==>`) are reported unused even when used, in every variant tried
  (renaming `-->`, `Hom` or `Self`, with or without other imports), which is why `-Wunused:imports` is commented out in
  `build.sbt` and `pants.toml`.
- **`export` of a stable member** (`export F.K`) creates a stable alias: `import K.{Obj, -->}` and singleton chains
  keep working. Moving `K` from a `val` to an export removed the `-Wsafe-init` warnings of `OptionT` and `StateT`.
- **Infix types** follow the precedence of term operators by first character: `*` > `+`, `-` (`-->`, `->>`) > `=`
  (`==>`) > `^` > letters (`is`), with `<` (`<->`) between `=` and `+`; `~>` and `~~>` bind tightest. Parenthesize mixed
  arrows and tensors. **Term operators** follow the same rule: `?<` binds tighter than every other operator, so
  parenthesize its operands, as in `(p >> q) ?< (p2 >> q2)`. After a space or an opening bracket, Scala reads `<?` and
  `<!` as the start of an XML literal, which is why the preorder's operator is not `<?`.
- **`-Wsafe-init`** warns on `tracked` parameters forwarded to a parameterized parent from a class, never from an object,
  which is why it is off (rule 11 of §4.1).
- **No given whose `Self` is `Nothing`** (rule 12 of §4.1).
- **Overlapping givens are ambiguous.** A generic given and a more specific one in the same object both match
  (`[A: Eq] => A is Observable` and `[A: Observable, B: Observable] => (A, B) is Observable` for `(Int, String)`),
  and Scala 3.10.0 reports an ambiguity. Put the fallback in a parent trait of the companion
  (`object Observable extends ComponentwiseObservable`): inherited givens rank below the companion's own.
- **`CanEqual` is not an equality.** It only permits `==`, whose meaning is the class's `equals`: reference identity on
  plain classes, not reflexive on `Double`. `Eq` instances on primitive data are named givens built with
  `Eq.structural`, never derived from `CanEqual` by a given.
- **Extensions shadowing methods** with the same signature need `(using DummyImplicit)` on the nullary extension.
- **Wildcards**: `import M.{*, given}` imports everything; `import M.{*, ***}` is an error, since `*` already imports
  `***`. To import a structure's infix alias `*` alone, backtick it: ``import M.{I, `*`, given}``.
- **Capture checking in tests**: a lambda inside ScalaTest's `assert(...)` macro can fail with "Illegal capture
  reference"; compute the value outside the macro (`StrictParserTest.result`). Lambda parameters whose types come from
  ScalaCheck (`Gen.zip(...).map((f, g) => ...)`) are inferred as capturing; annotate them with pure types. A method of
  the test class called from a generator lambda captures `this`; put such helpers in an object (`Descent`).
- **Match types and capture checking.** The product category's morphism type uses the match types `Fst`/`Snd`.
  Generic code never reduces them (the object evidence speaks about `Fst[X]` directly). Concrete code does, but under
  capture checking a `given` declared with an unreduced type (`given (K.-->[(Int, Long), …] is Observable)`) fails:
  the re-check puts a capture variable on `(Int, Long)` and the match type no longer reduces. Declare such givens in
  reduced form (`given ((Int -> String, Partial[Long, Boolean]) is Observable)`); values with an expected type are
  fine.
- **Scala 3.10 and capture checking.** The upgrade from 3.9.0 needed three kinds of change. Patterns of case classes
  without fields (`Proj1()`, `Success()`) crash the capture checker or fail with `Found: Proj1[…]`, `Required: Boolean`
  (`docs/DESIGN.md` §10): write type patterns, `case _: Proj1[?, ?]`, which match the same values and refine the same
  type arguments. A polymorphic function type cannot wrap an impure function type: write `[X] => Sample[X] ?->
  Sample[F[X]]`, not `?=>`. Scalameta rejects these pure arrows, so `scala_override` reads `?->` as `?=>`; `->` there
  has no such rewrite and is best avoided (`JsonGrammarTest` calls the algebra's `parse` instead of taking a function).
  And in a public inline method, the singleton type of a private member (`isInstanceOf[Failed.type]`) goes through an
  accessor, which is not a stable path: compare with `eq`. `Any.equals` is deprecated: use `==` with a `CanEqual`.
- **Inline methods and path-dependent givens.** Inside an inline expansion the algebra appears as a proxy path, so a
  given defined in the algebra is not found for the caller's `parser.P`; and an abstract type constructor cannot take
  wildcards (`P[?, ?]`). Evidence about the caller's types goes in a `using` parameter, resolved at the call site
  (`ParserAlgebra.Parsers` for `recursive[T <: Tuple]`).
- **sbt 2** caches task results, which needs a hash for every input; tasks with side effects need `Def.uncached`.
  `test` is incremental; use `testFull`. Cached compilation does not replay warnings: to see every warning, compile
  from scratch. The compile cache can also restore **stale class files**: after `Observable` changed from an abstract
  class to a trait, tests failed with `IncompatibleClassChangeError` even after `clean`, while a from-scratch `scalac`
  build passed. `clean` together with any source edit forces a fresh compile. sbt 2.0.10 restored semanticdb files as
  read-only symlinks into its cache, so the next recompile failed with `AccessDeniedException` (sbt#9877, fixed in
  2.0.11).
- **scalafmt 3.11.3** cannot parse some given syntax (§7); **Pants** requires the `scala_override` plugin with `Scala3Future` to parse `tracked` (§2).
- **Spikes first.** For a question about what the type system accepts, a twenty-line spike compiled at the library's
  version, `scala compile --server=false -S 3.10.0` with each flag passed as `-O flag` (Scala CLI, so that the
  system's `scalac` does not matter), answers faster than editing the library (the product category, renamed imports and infix
  precedence above were all settled that way).

---

## 12. Design rationale

`docs/DESIGN.md` is the design rationale: the goals, the decisions and their reasons, the alternatives that were
rejected, what the library leaves out and why, the compiler issues to file, and the open issues. Treat the decisions as
settled; reopen one only with a new argument, and record the result there.
