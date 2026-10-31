# Design rationale

Why Parrot is built the way it is: the decisions behind the categorical library and the parser, the alternatives that
were rejected, and the problems that remain open. The rules that follow from these decisions are in
[`CLAUDE.md`](../CLAUDE.md); the mathematics is explained in [`TUTORIAL.md`](TUTORIAL.md). The design was settled in a
review in October 2026 and revised while it was implemented; this document states the result. Treat it as settled,
and reopen a decision only with a new argument.

## 1. Goals

For the tutorial:

1. Close the gap between "programming with categories" and category theory: say precisely which programs, which
   equality and which category are meant.
2. Teach readers without a background in category theory to define their own categories in Scala, and what that commits
   them to.
3. Be honest about every claim: status tags, a ledger of assumptions, references per chapter, nothing unmotivated.
4. Keep the meta-language, Scala and the language of categories apart, and introduce concepts in a clean order.
5. Stay practical: sampling for equality, capture checking for purity, Stainless or a promise for totality.

For the library:

6. A faithful encoding: each construct is the mathematical notion, not an approximation.
7. Generality where the mathematics allows it.
8. Each notion defined once: no parallel hierarchies, derived structure wherever possible.
9. Symmetry across the hierarchy: no unexplained asymmetries.
10. `extends` only for refinements of the same notion; structure *on* something takes it as a parameter.
11. Everything lives inside 𝒮, so 𝒮 is the ground.
12. Usable in real code: plain syntax, designs that compile without casts.
13. The tutorial and the library justify each other: the library should read as a consequence of the tutorial, and the
    tutorial must cover everything in the library. When the two disagree, prefer pruning the library to padding the
    tutorial.

The category library stands on its own; the parser is its first and most important client.

## 2. Two categories of programs

**Decision.** There are two categories of Scala programs. 𝒮 (`Total`) has the pure, total functions `A -> B`. 𝒫
(`Partial`, an opaque alias of `A -> B`) has the pure programs that may not terminate, written `Partial(f)`.
`Partial.fromTotal(f)` includes 𝒮 in 𝒫; `Partial.assumeTotal(p)` is the library's single, greppable promise of
totality. `=>` functions have no category instances. Purity (`->` versus `=>`) and totality (𝒮 versus 𝒫) are separate
axes; both categories require purity.

**Why.** A bicartesian closed category with a fixed point for every endomorphism collapses (tutorial, Proposition 14.3),
so 𝒮 cannot have general recursion or iteration. The earlier library had such operators on `Function`, and each of them
diverged on some input while claiming to be an arrow of a total category; the Conway fixed point of `not ∘ π₂` would
have been a `Boolean` equal to its own negation. Placing unguarded recursion and loops in 𝒫, and guarded ones in 𝒮,
removes the contradiction. Formally, 𝒫 is a restriction category whose total arrows are exactly 𝒮 (Cockett and Lack),
its pairs are restriction products, and the tutorial's formal core is a strict partial language whose total part,
defined by a logical relation by induction on types, is 𝒮.

**Rejected.** Lazy pairs as the product (`LazyTuple2`): isomorphic to ordinary pairs in 𝒮, and not a product in 𝒫,
where a program can tell a diverging pair from the pair of its diverging components. This is Bauer's objection to
"Hask is Set", in Scala.

## 3. The encoding

**Decisions and reasons.**

- **Structures take what they are built on as `tracked` term parameters**: `Strong(P, L1, L2)`, `Promonad(K)`,
  `Monad(F)`. A term parameter is a stable path, so its type members can be named and imported; `tracked` keeps its
  singleton type in the instance's type, so `Kleisli.OptionKleisli.K` is known to be `Total`. The earlier encoding
  passed bases as type parameters, which cannot be imported from, and recovered the base values with `ValueOf` and
  casts (16 `asInstanceOf` and 17 `Of[...]` traits). The encoding was validated by a spike (in the git history, under
  `docs/redesign/spike`, until commit `2f16e14`) before the library was rewritten: no casts, all laws pass.
- **What a structure is on is a parameter; what it adds is a member.** A monoidal structure is on a category, a unit
  object and a tensor, `Monoidal(K, U, T)`, and names their types `I = U.Self` and `Tensor = T.F`; `tracked` makes them
  known to clients (`Total.Product.I` is `Unit`) without a member that every instance restates. The unitors, the
  associator and the braiding are members, because refinements derive them (`Cartesian`), and so is the internal hom,
  which is what `Closed` adds: ⊗ determines it up to isomorphism, and evaluation and currying determine its action on
  morphisms (`Closed.InternalHom`). The unit's evidence `U` is a value parameter, not a context parameter or an abstract
  given: 𝒮 has two units and two tensors, so implicit search cannot choose them (for a `using` parameter it chose
  `Type.TIsType[Any]`), and `deferred` givens are allowed only in traits. The structure offers the evidence to its
  clients as a given, `IIsObj`.
- **Structures are abstract classes**, because a refinement passes arguments to its parent (`Promonad(K)` extends
  `Endoprofunctor(K, Total)`) and a trait cannot pass arguments to a parent trait. **Type classes without parameters that
  are not categorical structures** (`Type`, `Eq`, `Observable`, `Preorder`, `Measure`) are traits.
- **`Self` only when the structure has its own carrier** (a category's morphisms, a functor's object map, a monoid's
  object). Structures *on* something else (`Monoidal`, `Module`, `Strong`, `Restriction`, the grid, `Monad`) have no
  `Self` and are named, not found by carrier: 𝒮 carries both products and coproducts, and nothing about the carrier
  tells them apart.
- **Combinations are bundles, not inheritance.** A class that extended a product and a coproduct structure would
  inherit two `Tensor`s, two `I`s and two `braid`s. `Freyd(S)` and `ParserAlgebra(...)` take their structures as
  parameters instead.
- **Objects are types with evidence**: a category declares `type Obj <: Type`, and evidence travels only through
  context bounds, which come after the value parameters, so that infix code infers its types. Evidence classes such as
  `Eq` extend `Type`, so evidence search is sound but not canonical (the tutorial discusses coherence).
- **Names follow the mathematics.** Carriers have short aliases (`Hom`/`-->`, `F`, `P`, `M`, `C`); arrows of other
  categories are imported, renamed where categories meet (`->>`, `==>`, `~~>`); these three-symbol arrows name roles,
  while the two concrete categories have two-symbol arrows, `->` for 𝒮 and `~>` for 𝒫; objects are combined infix (`*`,
  `+`, `B ^ A` for *B*ᴬ, `<->` for isomorphisms); every structure has its own operators (`>>>`, `>>`, `***`, `&&&`,
  `|||`, `**`, `|>`, `=?=`, `?<`, `===`), so two structures can be imported into one scope, and none is a name that a
  type already has: `?<`, not `<=`, which `Int`'s own `<=` would shadow. Plain forwards are `export`s.
- **A monad is structure on an endofunctor**: `Monad(F: Endofunctor)` with `unit` and `flatten` primitive, the monoid
  presentation, so that `Monad` and `Monoid` have the same shape; `bind` is derived. Monads are refined through their
  functor (`Monad.On[Total.type]`), because only that keeps the chain of singleton types that path-dependent code needs.
- **Products of categories use match types.** `Category.Product(C1, C2)` has pair types as objects. A morphism type is
  computed from two object types, and the only way to take a type apart at the type level is a match type
  (`Fst[(A1, A2)] = A1`): evidence is a value and cannot index a type, and projecting a type member of an abstract type
  is unsound. The object evidence speaks about `Fst[X]` and `Snd[X]` directly, so generic code never needs a match type
  to reduce. A bifunctor keeps its own two-parameter carrier and `bimap`, and is related to `Functor` by the view
  `Bifunctor.functor` (like `Promonad.category`), whose functor laws are the bifunctor laws. Making `Bifunctor` extend
  `Functor` would put match types into every instance's signatures; a separate class for categories whose objects are
  pairs of types would duplicate `Category` (tutorial, chapter 10).

## 4. The structures, and the level each lives at

Each structure sits at the lowest level where its laws can be stated.

| Row | Over products | Over coproducts | Level |
| --- | --- | --- | --- |
| strength | `Bistrong` (⊗ = ×) | `Bistrong` (⊗ = +), also called choice | `Strong`: a profunctor over left modules (a Tambara module); `Bistrong`: over a symmetric **K** acting on itself |
| trace | `Traced` (×) | `Traced` (+) | a bistrong promonad: superposing needs composition and strength |
| fixed point | `Conway` | `Elgot`, which is `Conway` on *P*ᵒᵖ | a bistrong promonad |

- `Strong` and `Traced` are defined once, parameterized by the monoidal structure. The earlier `Strong extends
  Monoidal`, with `first = p *** id`, was vacuous: every one of its laws followed from bifunctoriality.
- **Strength over left modules.** `Strong(P, L1, L2)` is a profunctor *P*: **K₁**ᵒᵖ × **K₂** → 𝒮 with left actions
  `Module` of one monoidal **M** on **K₁** and **K₂**, and its primitive is the left strength *τ*: *P*(*A*,*B*) →
  *P*(*C* ⊘₁ *A*,*C* ⊘₂ *B*), `left`, as in the literature (Pastro and Street's Tambara modules; Moggi's strength is a
  left strength). §8 listed actegories as not attempted; they came in because the general definition costs nothing:
  every instance in the library is the self-action, which is a subclass. `Bistrong(P, M)` is that case for a symmetric
  **M** acting on itself, the only case with a right action as well: it adds the right strength *τ*′, `right`, and the
  law that the two commute (`compatibility`). *τ*′ defaults to *P*(*β*,*β*) ∘ *τ* and may be overridden, which
  `StrictParser` does to build `Zip(p, Success())` directly. `Freyd` names the strengths after the component an arrow
  runs on, `first` = *τ*′ and `second` = *τ*, so the laws of Freyd categories and the grid read as usual.
- Rejected: naming the primitive `first` (with a left action it runs an arrow on the *second* component, and every
  client read backwards); `Bistrong` over two arbitrary left modules (a left module has no right action, so *τ*′ would
  be *τ*: it needs right modules, or bimodules, which have no client); `Bistrong` refining `P { val K1: M.K.type; val
  K2: M.K.type }` (for a promonad, nothing makes its own **K** equal to **M**.**K**; the constraint refines **M**
  instead); separate duals over products and coproducts (one `Bistrong.Op(S, S.M.op)`, whose braiding is not checked).
- A Freyd category is a promonad with a strength and two compatibility laws, not a new class.
- The trace laws restrict sliding and superposing to pure arrows, which are central (traced *premonoidal* categories).
- The product row has no useful total instance in a strict language: computing ⟨*id*,*p*†⟩ ⨾ *p* requires *p*† first.
  Its instances exist by duality, on 𝒫ᵒᵖ, and the bridges (`OfElgot`, `OfConway`, `OfTraced`) are tested in both rows.
- Recursion at the types of arrows, `Recursion`, is a fixed point in 𝒮 at the type *P*(*A*,*B*), not an operation of
  the category of arrows; a grammar rule refers to itself as a value. In 𝒫 it ties the η-expanded knot; in 𝒮 it is
  guarded. Mutual recursion is a fixed point of a family of arrows, `fixFamily`, with one knot per arrow. Solving the
  family one arrow at a time by Bekić's theorem would also work, but it applies the definition exponentially often in
  the number of arrows, and a guarded instance cannot share its guard between separately tied knots.
- Guarded iteration and recursion (`StateT.GuardedIteration`, `StateT.GuardedRecursion`) are total by construction
  and lawful on guarded arguments, after Goncharov and Schröder; yanking fails for the guarded trace, which is recorded
  as a counterexample.
- Restriction: `Restriction` has R1–R4; `Classical` adds the restriction zero, complements and override ⊳ with the
  axioms of Lemay and Nester, which make PEG ordered choice a theorem rather than an invention. Postcomposition does
  not distribute over ⊳; precomposition does.
- Comonoids are the dual of monoids. Every object of a cartesian category is a comonoid in exactly one way; pairs in 𝒫
  have comonoids that programs do not preserve, which by Fox's theorem is why they are not products.
- **One level of enrichment.** A category with a semantic equality on its homs and congruence laws is enrichment over
  setoids, stated directly; parsers with a preorder on their homs are enrichment over preorders, stated directly. The
  earlier parallel hierarchy of enriched categories, functors and promonads, joined to the ordinary one by bridges and
  casts, was removed. An enriched module may come back as an opt-in package once it has a client.

## 5. Laws, and how they are checked

- `Eq` is **semantic equality on data**, with equivalence laws, and every operation that consumes it has a congruence
  law. Functions have no `Eq`.
- `Observable` is the **law-checking oracle**: finitely many observations ending in data compared with `Eq`. It is
  deterministic and pure, and sound for refutation. Sampled agreement is an equivalence but not a congruence, so
  congruence laws take *variants*, values equal by construction. `Preorder` is its counterpart for inequations.
  Both have laws of their own, tested for every observation the law tests use: agreement is an equivalence and an order
  is a preorder; both are *sound*, since variants agree and are ordered both ways; and an order contains agreement,
  for an `Observable` that makes the same observations. That congruence fails is a counterexample test.
- Randomness lives only in generators, and **sample points are generated per property**. Arrows come from sharp
  generators (failure, partiality, consumption); conditional laws use targeted generators instead of `==>`.
- Iteration and fixed-point operators satisfy dinaturality for all arrows, effectful ones included, not only for pure
  ones.
- One generic specification per structure, one test class per instance. Laws known to fail are **counterexample
  tests**, which must find a witness: they document the intended semantics as much as the laws do.
- A specification takes the **instance it checks**, with what its laws need of it in the parameter type (objects that
  are all types), and finds the instance's fixture as a given: one per category or promonad. Passing the fixture
  instead hid the category inside it, and with it the constraint on the category's objects. Fixtures of derived
  categories (`Total.op`, `P.category`) are written as givens of their own, because implicit search cannot get from
  `Total.op` back to `Total`.
- Every test run regenerates **`docs/law-status.md`**, the table of laws, instances and statuses that the tutorial's
  status tags cite. The tests write it themselves, which keeps it independent of the build tool.

## 6. The parser

- **The algebra is a bundle**: `ParserAlgebra(Arrows, Products, Coproducts, Zipping, Branching, Choice, Loops, Knots)`,
  every combinator an operation of one of them. An interpreter chooses the structures and implements five primitives:
  `lift`, `literal`, `regex`, `rule`, `diagnose`. The semantic types are fixed (`Unit`, `Tuple2`, `Either`, `Nothing`,
  `Vector`); every interpreter made the same choice, and fixing them removes a layer of type members.
- **Ordered choice is override**, derived from the classical structure; `attempt(p): P[A, B + A]`, which runs `p` once
  and reports the outcome, is the form an optimizing interpreter can implement in one pass. `optional` is `attempt`.
  The second alternative is computed only where the first fails, also in the reference, whose classical monad takes
  it by name.
- **Regular expressions are matched in context and by code point**, as `java.util.regex` matches them: `^`, `$`,
  lookbehind and `\b` see the whole input, and a surrogate pair is one character. The optimizing interpreter compiles
  a fragment of them to a scanner that agrees with `java.util.regex` on it, including on surrogates.
- **Iteration and recursion are guarded by the input**: a loop step that continues, or a recursive call, must come after
  consumed input, or it fails. Every parser therefore terminates, and repetition of an item that consumes nothing fails
  instead of looping or stopping silently.
- **The reference interpreter builds nothing new**: it is the Kleisli category of
  `StateT[Input](OptionT(Writer(Expected.Furthest)))`, and every structure is a generic construction of the library. It
  is the specification, meant to be obviously right, and it is slow.
- **The optimizing interpreter normalizes by laws**: its smart constructors are laws read from left to right, so they
  cannot change what a parser does. Its one analysis that is not a law, the first-set summary `Info`, carries an
  invariant (if a parser succeeds where the next character is `c`, then `c ∈ first`, or it is nullable and consumed
  nothing), and the random law tests check it indirectly; they found a violation once. It dispatches choices on the next
  character, records no diagnostics on the fast path, and re-runs in a diagnostic mode only when a parse fails.
- **Agreement is the core invariant**: both interpreters give the same results, offsets and diagnostics on every grammar
  without left recursion, checked by random grammars, the law specifications and the JSON grammar. `StrictParser`
  supports left recursion by seed growing, an extension beyond the specification, where the reference fails the
  left-recursive call.

## 7. Diagnostics

- A parse reports the furthest position at which something failed and the set of expectations there, each tagged with
  the rules that enclose it. The reports form a join-semilattice, the lexicographic product of the chain of positions
  with sets of expectations, and they are a **writer effect**, produced on success as well as on failure.
- The laws force most of this: the choice monoid needs an associative combination with a unit, and distributivity,
  `h >> (p |> q)` = `(h >> p) |> (h >> q)`, runs `h` twice, which is harmless only if *x* ⊔ *y* ⊔ *x* = *x* ⊔ *y*.
  Commutativity is a choice: it makes the report independent of the order in which alternatives were tried.
- **Tests are silent**: lookahead, negation, `failure` and guard failures report nothing. Keeping the output of a test
  breaks R2 for every writer with a non-trivial output, because a failing test stops the output after it, and breaks
  the zero and complement laws as well (the tests in `RestrictionTest` exhibit both). Silent tests keep R2, R3 and the
  complement laws exact and weaken only R1 and R4 to inequations.
- `rule(p, l)` reports `l` where `p` fails at or before its start, and otherwise adds `l` to the context of `p`'s
  expectations; tagging preserves joins.
- The laws come in **two tiers**: equations on results, offsets and diagnostics, and inequations *p* ⊑ *q* (same
  results and offsets, *q* reports at least what *p* reports) for right zero, R1 and R4. Every combinator is monotone
  for ⊑, so parsers are enriched over preorders.

## 8. What the library leaves out

Removed in the redesign; the last commit that contains all of them is tagged `pre-prune`.

| Construct | Why it was removed | Bring it back when |
| --- | --- | --- |
| Total fixed points and iteration on `Function` (`FunctionIsLazyCartesianConway`, `FunctionIsLazyCartesianTraced`, `FunctionIsCocartesianTraced`, `FunctionIsCocartesianElgot`, `FunctionIsFixed`, `OptionIsElgotMonad`, `TryIsElgotMonad`) | Each diverged on some input while claiming to be an arrow of 𝒮 (§2). | Never; see `Partial` and the guarded operators. |
| `LazyTuple2` and its instances | Isomorphic to `Tuple2` in 𝒮, not a product in 𝒫. | A lazy semantics becomes a target. |
| `Strong extends Monoidal` | Vacuous. | Never in this form. |
| `Fixed` (`ExponentialIsFixed`, `Tuple2IsFixed`, `FunctionIsFixed`) | Replaced by `Recursion` (§4), whose `fixFamily` also covers mutual recursion. | Never. |
| `FunctionIsRestriction` | The identity in 𝒮; meaningful on 𝒫, as `Partial.Domains`. | Never. |
| `Pointwise`, `Valued`, `Monoid.Additive` instances | Presented ordered choice as enrichment over additive monoids, which it is not: choice distributes on one side only. | Never. |
| `Monoid.Multiplicative` | No client. | A client appears. |
| `EnrichedCategory`, `EnrichedFunctor`, `EnrichedPromonad` | A parallel hierarchy (§4). | An enriched module gets a client. |
| `Pair`, `Isomorphism` (trait), the `Of[...]`/`ValueOf` traits | Artifacts of the cast-based encoding (§3). | Never. |
| `PureFunction` | Replaced by `Total` with `->` under capture checking. | Never. |
| `Try` instances | The reference reports diagnostics through a writer instead; `TryIsEq` identified all failures, which nothing respected. | A client appears. |
| Mixin traits of the parser algebra, abstract semantic types, `ParserAlgebra.Standard` | Replaced by the bundle and fixed semantic types (§6). | An interpreter needs other semantic types. |
| `=:=` instances, `OptionNothingIsoUnit` | Examples, not structure. | As tests or tutorial material. |
| `CanEqualIsEq`, a given `Eq` for every type with a `CanEqual` | `CanEqual` only permits `==`; it would have made reference identity an `Eq` on plain classes, and an `Eq` on `Double` that is not reflexive (`NaN`). | Never; `Eq.structural` states the claim per type. |

Brought back after being removed: `Comonoid`, as the dual of `Monoid` and for Fox's theorem (its old version added
nothing and named its operations `zero` and `add`); and the product of categories, as the cast-free `Category.Product`
(its old version recovered objects from type parameters with casts).

Not attempted, each until it has a client: codata and productivity, restriction products as a class, useful fixed
points over products in a strict language, packrat memoization, error recovery, an enriched module, right modules and
bimodules, module morphisms, mixed optics, general iterated enrichment, the delay monad.

## 9. Tooling

- **Tests run in a forked JVM** with an explicit heap, and the JSON corpora are parsed on a thread with an explicit
  stack, so that the outcome does not depend on the defaults of the machine; every corpus document is asserted on
  both interpreters.
- **sbt and Pants.** Pants builds use the `scala_override` plugin to configure its Scalameta parser with
  `Scala3Future`, enabling dependency inference for `tracked` parameters.
- **Capture checking everywhere**, in the library and in the tests, so that `->` means a pure function wherever it is
  written. ScalaCheck is not compiled with capture checking, and its generated functions are trusted to be pure.
- **The tutorial's code is compiled** by `docs/tutorial/check-snippets.py`, a script rather than a build task, so that it
  works the same with any build tool.

## 10. Compiler issues to file

All three have been verified with Scala 3.10.0. The first two are worked around by turning the flags (`-Wsafe-init`,
`-Wunused:imports`) off in `build.sbt` and `pants.toml`, the third by type patterns.

**`-Wsafe-init` false positive when a `tracked` constructor parameter is forwarded to a parent class.** Options:
`-source:future -language:experimental.modularity -Wsafe-init`.

```scala
abstract class Base(tracked val x: AnyRef)
abstract class Middle(tracked val y: AnyRef) extends Base(y)

class ViaClass extends Middle("a")   // warning: Access non-initialized value y
object ViaObject extends Middle("a") // no warning

abstract class PlainBase(val x: AnyRef)
abstract class PlainMiddle(val y: AnyRef) extends PlainBase(y)
class PlainClass extends PlainMiddle("a") // no warning

@main def run(): Unit = println((ViaClass().x, ViaObject.x, PlainClass().x))
```

The program prints `(a,a,a)`: `y` is initialized when it is used. The same chain instantiated by an `object`, or
written without `tracked`, produces no warning.

**`-Wunused:imports` reports a renamed type import as unused although it is used.** Options: `-Wunused:all`.

```scala
trait Box { type T }

class Uses(val b: Box) {
  import b.T as U // warning: unused import
  def f(u: U): U = u
}
```

Without the rename (`import b.T` and `T` in the signature) there is no warning. The same happens for type aliases and
abstract type members, with or without braces around the selector, and with or without other imports in scope.

**Capture checking mis-types patterns of case classes without fields.** New in Scala 3.10.0, and still in 3.10.1-RC1.
Options: `-language:experimental.captureChecking`.

```scala
sealed trait Fn[A, B]
final case class Id[A]() extends Fn[A, A]
final case class Fst[A, B]() extends Fn[(A, B), A]
final case class Snd[A, B]() extends Fn[(A, B), B]

def isId[A, B](f: Fn[A, B]): Boolean = f match {
  case Id() => true // error: Found: Id[A], Required: Boolean
  case _    => false
}

def both[A, B, C](f: Fn[A, B], g: Fn[A, C]): Boolean = (f, g) match {
  case (Fst(), Snd()) => true // crash: unexpected type of Fst.unapply(...).&&
  case _              => false
}
```

Scala 3.9.0 compiles both. The pattern matcher combines the `unapply` of a case class without fields with `&&`, as a
`Boolean`, but capture checking types it as returning the case class. A type pattern, `case _: Id[?]`, matches the same
values and refines the type arguments the same way; `Fn`, `StrictParser` and the tutorial use it.

Two more behaviors cost time but are not clearly bugs: under capture checking, a `given` declared with an unreduced
match type fails, because the check adds a capture variable to the scrutinee (declare it in reduced form); and sbt 2's
compile cache once restored class files that were stale after a class became a trait (`clean` plus a source edit forces
a fresh compile).

## 11. Open issues

None are known. The reviews of the earlier library raised problems that the redesign did not resolve at first: the
scanner matched `Char`s instead of code points, the reference evaluated both alternatives of a choice, tuple recursion
applied its definition exponentially often, a failure that expected nothing was reported at position −1, regular
expressions were matched out of context and by copying the rest of the input, dinaturality was stated only for pure
arrows, the JSON corpora were not asserted, and their exclusion list depended on the stack size. Each is fixed and
covered by a test. The compiler issues of §10 remain to be filed.
