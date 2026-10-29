# How the structures relate

The structures of `parrot.category` are built from one another. This document maps how: what each structure is a
structure *on*, what it refines, what it is a special case of, what it is dual to, and what it induces. The tutorial's
concept index (Appendix E of [`TUTORIAL.md`](TUTORIAL.md)) says where each concept is introduced, and
[`DESIGN.md`](DESIGN.md) §4 at which level each one lives.

## Kinds of relation

| Relation | In the code | Examples |
| --- | --- | --- |
| *on*: structure on something else | a `tracked` parameter | `Monoidal(K, U, T)` on a category, a unit object and a bifunctor; `Monad(F)` on an endofunctor; `Restriction(P)` on a promonad |
| *refines*: more operations and laws | `extends`, forwarding the parameters | `Symmetric` refines `Monoidal`; `Cartesian` and `Cocartesian` refine `Symmetric`; `Classical` refines `Restriction`; `Semilattice` refines `Monoid` |
| *is a*: a special case of something more general | `extends` with fixed arguments, or a view | an `Endofunctor` is a `Functor` from **K** to **K**; a `Bifunctor` is a `Functor` out of a product (`FromProduct`); a `Profunctor` is a `Bifunctor` out of **K**ᵒᵖ × **K** |
| *dual*: the same structure on the opposite | an `Op` class | `Category.Op`; `Cartesian.Op` is `Cocartesian`; `Promonad.Op`; `Conway.OfElgot` |
| *induces*: a construction from one structure to another | an `open class` or a method | a category gives a promonad (`Promonad.Hom`); a monad gives a promonad (`Kleisli`); a monoid gives a monad (`Writer`); a semilattice gives a preorder (`Preorder.of`) |
| *bridge*: two structures that define each other | `Of…` classes | `Traced.OfElgot` and `Elgot.OfTraced`; `Traced.OfConway` and `Conway.OfTraced` |
| *bundle*: structures used together | a class of `tracked` parameters | `Freyd(S)`; `parser.ParserAlgebra` |

## The map

```
Type ─ refines ─ Eq ─ induces ─ Observable ─ counterpart ─ Preorder            evidence and oracles

Category (Op, Product, Iso)                                                    𝒮 = Total, 𝒫 = Partial
└─ on ─ Functor ─ is a ─ Endofunctor ─ on ─ Monad ─ induces ─ Kleisli (a Promonad)
   │                                         ├─ on ─ RestrictionMonad ─ ClassicalMonad, ElgotMonad
   │                                         └─ transformers: Writer (from a Monoid), OptionT, StateT
   └─ Bifunctor ─ is a ─ Functor out of Category.Product
      ├─ on ─ Monoidal ─ refines ─ Symmetric ─ refines ─ Cartesian ⇄ Cocartesian (dual)
      │       ├─ on ─ Closed
      │       └─ on ─ Monoid ⇄ Comonoid (dual); Semilattice (on Cartesian) ─ induces ─ Preorder
      └─ Profunctor ─ is a ─ Bifunctor out of Kᵒᵖ × K
         └─ refines ─ Promonad (Underlying, Op, Hom)
            ├─ on ─ Strong (+ Symmetric) ─ bundle ─ Freyd
            │       └─ on ─ Traced ⇄ Conway (+ Cartesian), Elgot (+ Cocartesian)   bridges and duals
            ├─ on ─ Restriction ─ refines ─ Classical (+ Cocartesian)
            └─ on ─ Recursion
```

The concepts form three branches that meet in the parser: **tensors** (monoidal structure and the monoids in it),
**effects** (promonads and the structure on them), and **monads**, which are one way to build effects.

## Evidence and oracles

`Type` is the object evidence every type has; a category states its objects with a refinement `Obj <: Type`, and `Eq`
is the refinement that selects data, the types with a decidable equality. `Observable` and `Preorder` are not
categorical structures but the oracles that laws are checked with: `Observable` decides agreement on finitely many
observations, each ending in data compared with `Eq`, so every `Eq` type is observable; `Preorder` is its inequational
counterpart and contains agreement. A semilattice induces a preorder (`Preorder.of`): *a* ⊑ *b* iff *a* ⊔ *b* = *b*.

## Categories

A `Category` has types as objects (with evidence `Obj`) and values as morphisms. Three constructions make categories
or morphisms from categories: the opposite `Op`, whose morphisms are reversed and which every duality below goes
through; the product `Product`, whose objects are pairs and which is the source of a bifunctor; and the isomorphisms
`Iso`, which a monoidal structure's unitors, associator and braiding are.

Everything else is structure on two categories, or on categories built from them: 𝒮 (`Total`), the total pure
functions, and 𝒫 (`Partial`), the pure programs that may diverge. 𝒮 is the subcategory of 𝒫 of total programs:
`Partial.fromTotal` includes a morphism of 𝒮, and `Partial.assumeTotal` promises totality.

## Functors

A `Functor` maps one category to another, as the inclusion of 𝒮 in 𝒫 does (`Partial.Inclusion`); an `Endofunctor` maps a
category to itself and is what a monad is structure on. A `Bifunctor` is a functor of two arguments, read as a functor
out of the product category through its view `functor` (`Bifunctor.FromProduct`), whose functor laws are its laws. A
`Profunctor` is a bifunctor out of **K**ᵒᵖ × **K**: contravariant in its first argument, as `A -> B` is in `A`; `dimap`
is its morphism part with the variance spelled out. The tensors of 𝒮 and 𝒫, pairs and tagged unions, are bifunctors
(`Tuple2IsBifunctor`, `EitherIsBifunctor`).

## Tensors

A `Monoidal` structure is on a category, a unit object *I* and a bifunctor ⊗: **K** × **K** → **K**, with isomorphisms
that make ⊗ associative and unital. `Symmetric` adds the braiding, which swaps the arguments. `Cartesian` and
`Cocartesian` refine `Symmetric` where the tensor is a universal construction: the product, with a terminal unit, and
the coproduct, with an initial unit. They are dual: `Cartesian.Op` reads the products of **K** as coproducts of **K**ᵒᵖ,
with the tensor as a bifunctor on **K**ᵒᵖ (`Cartesian.Tensor`), and `Cocartesian.Op` the converse. `Closed` is on a
monoidal structure: an internal hom *A* ⇒ *B* with evaluation and currying.

𝒮 has all of them: products, coproducts and function types (`Total.Product`, `Total.Coproduct`,
`Total.Exponential`). 𝒫 has coproducts, but its pairs are only symmetric monoidal (`Partial.Product`):
*π*₁ ∘ ⟨*f*,*g*⟩ diverges where *g* does.

## Monoids in a monoidal category

A `Monoid` is an object of a monoidal category with a unit *I* → *M* and a multiplication *M* ⊗ *M* → *M*; in 𝒮 with
pairs, an ordinary monoid. A `Comonoid` is its dual, an object that can be deleted and copied. A `Semilattice` is a
commutative, idempotent monoid, which needs the braiding and the diagonal of a cartesian category.

- In a cartesian category every object is a comonoid in exactly one way (`Cartesian.comonoid`). The pairs of 𝒫 have
  comonoids too (`Partial.Product.comonoid`), but programs do not preserve them, which is why they are not products.
- A monoid in 𝒮 induces a monad, the writer (`Writer`), and a semilattice a preorder (`Preorder.of`).
- A monad is a monoid in the endofunctors and a promonad a monoid in the endoprofunctors, with composition as the
  tensor. Neither is a `Monoid` of the library: endofunctors and profunctors are type constructors, and the objects
  of a category are types of kind \* (tutorial ch. 10).

## Promonads

A `Promonad` on **K** is a profunctor valued in 𝒮 with a unit, which embeds the morphisms of **K**, and a
multiplication, which composes arrows: a category of arrows built on top of **K** (`Promonad.Underlying`, the category
`P.category`), with an opposite (`Promonad.Op`). Two constructions give promonads: every category is one over itself
(`Promonad.Hom`: `Total.Functions`, `Partial.Programs`), and every monad gives one, its Kleisli arrows (`Kleisli`). All
the structure on effects below is on a promonad.

## Strength and Freyd categories

A `Strong` structure is on a profunctor and a symmetric monoidal structure of its base: `first` runs an arrow on one
side of ⊗ and passes the other side along. With the product, arrows run side by side; with the coproduct, on one side
of a tagged union (choice). It is defined once, for any monoidal structure. A `Freyd` category bundles a promonad with
a strength that its unit and multiplication preserve.

- Strengths are induced: a hom promonad is strong over its own symmetric monoidal structures (`Strong.OfHom`:
  `Partial.Parallel`, `Partial.Choice`), and the Kleisli promonad of every monad on 𝒮 is strong for products and for
  coproducts (`Kleisli.ProductStrength`, `Kleisli.CoproductStrength`).
- Strengths are dual: a strength over coproducts is a strength over products of **K**ᵒᵖ in the opposite promonad
  (`Strong.OpOfCoproduct`), and conversely (`Strong.OpOfProduct`).

## Restriction

A `Restriction` structure is on a promonad: every arrow *p* has a restriction *p̄*, the partial identity on the inputs
where *p* is defined. `Classical` refines it where the base has coproducts and definedness is decidable: a zero arrow,
complements, override ⊳ and `attempt`. 𝒫 is a restriction category (`Partial.Domains`) but not classical, since the
complement would decide termination. Functions that may fail are classical (`Kleisli.OptionDomains`), with failure as
zero and ordered choice as override: PEG ordered choice is a theorem of this structure.

## Iteration and recursion

Three operators on a strong promonad form a grid (`DESIGN.md` §4):

- `Elgot`, iteration, over coproducts: *p*: *P*(*X*,*A* + *X*) gives *p*†: *P*(*X*,*A*), run until it returns *A*;
- `Conway`, the parameterized fixed point, over products: *p*: *P*(*A* × *X*,*X*) gives *p*†: *P*(*A*,*X*);
- `Traced`, feedback, over either: *tr*(*p*): *P*(*A*,*B*) for *p*: *P*(*A* ⊗ *U*,*B* ⊗ *U*).

They are related twice. By duality, iteration is a fixed point read backwards: an Elgot operator on *P* is a Conway
operator on *P*ᵒᵖ (`Conway.OfElgot`), and conversely (`Elgot.OfConway`), through the dual strengths. And by bridges,
a trace gives iteration over coproducts and fixed points over products, and each gives back a trace
(`Elgot.OfTraced`, `Conway.OfTraced`, `Traced.OfElgot`, `Traced.OfConway`). In a strict language the product row has no
useful total instance; its instances exist by duality, on 𝒫ᵒᵖ.

`Recursion` stands apart: it is a fixed point in 𝒮 at the type *P*(*A*,*B*), not an operation of the category of
arrows, so it needs only a promonad and no strength. 𝒫 has all of these, unguarded: the while loop (`Partial.Loops`),
its trace (`Partial.Feedback`) and recursion by an η-expanded knot (`Partial.Knots`). In 𝒮 they must be guarded.

## Monads

A `Monad` is on an endofunctor, with a unit and a multiplication; `map` is the functor's, and `bind` is derived. Its
main relation is the promonad it induces, the Kleisli arrows *A* → *M*[*B*] (`Kleisli`).

- **Structure at the level of the monad.** Structure on the Kleisli promonad of a monad on 𝒮 can be stated on the
  monad: `RestrictionMonad`, its refinement `ClassicalMonad`, and `ElgotMonad`. Their laws are those of the Kleisli
  structures they induce (`Kleisli.RestrictionOf`, `Kleisli.ClassicalOf`, `Kleisli.ElgotOf`).
- **Transformers.** `Writer` makes a monad from a monoid in 𝒮; `OptionT` (failure) and `StateT` (state) make monads
  from monads on 𝒮. The failure transformer is classical (`OptionT.ClassicalOf`), and the state transformer lifts a
  classical structure, backtracking where an alternative fails (`StateT.ClassicalOf`).
- **Guarded iteration and recursion.** With a `Measure` on its states, the state transformer over a classical monad
  has total iteration (`StateT.GuardedIteration`, an `ElgotMonad`) and recursion (`StateT.GuardedRecursion`, a
  `Recursion` of its Kleisli promonad), which fail on a step or call that makes no progress.

## Where the branches meet: the parser

`ParserAlgebra` bundles one structure from each part of the map: a promonad of parsers (`Arrows`) over a category of
pure functions, its products and coproducts (`Cartesian`, `Cocartesian`), the strengths over both (`Zipping`,
`Branching`), a classical restriction structure for choice (`Choice`), iteration (`Loops`, an `Elgot` operator) and
recursion (`Knots`). `ReferenceParser` builds them all from the monad branch: the Kleisli promonad of
`StateT[Input](OptionT(Writer(Expected.Furthest)))`, whose diagnostics form a semilattice, ordered by the preorder it
induces.

## An order that follows the dependencies

Each item needs only those before it:

1. `Type`, `Eq`
2. `Observable`
3. `Category` (with `Op`, `Product`, `Iso`), `Total`, `Partial`
4. `Functor`, `Endofunctor`
5. `Bifunctor`
6. `Monoidal`, `Symmetric`
7. `Cartesian`, `Cocartesian`
8. `Closed`
9. `Monoid`, `Semilattice`, `Comonoid`, then `Preorder`
10. `Profunctor`, `Promonad`
11. `Strong`, `Freyd`
12. `Restriction`, `Classical`
13. `Elgot`, `Conway`, `Traced`, `Recursion`
14. `Monad`, `Kleisli`
15. `RestrictionMonad`, `ClassicalMonad`, `ElgotMonad`; `Writer`, `OptionT`, `StateT`

`Total` and `Partial` are categories in item 3; their instances of later structures belong to the item of the
structure.
