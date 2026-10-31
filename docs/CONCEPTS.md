# How the structures relate

The structures of `parrot.category` are built from one another. This document maps how: what each structure is a
structure *on*, what it refines, what it is a special case of, what it is dual to, and what it induces. The tutorial's
concept index (Appendix E of [`TUTORIAL.md`](TUTORIAL.md)) says where each concept is introduced, and
[`DESIGN.md`](DESIGN.md) §4 at which level each one lives.

## Kinds of relation

| Relation | In the code | Examples |
| --- | --- | --- |
| *on*: structure on something else | a `tracked` parameter | `Monoidal(K, U, T)` on a category, a unit object and a bifunctor; `Module(K, M, T)` on a category and a monoidal category acting on it; `Strong(P, L1, L2)` on a profunctor and two modules; `Monad(F)` on an endofunctor; `Restriction(P)` on a promonad |
| *refines*: more operations and laws | `extends`, forwarding the parameters | `Symmetric` refines `Monoidal`; `Cartesian` and `Cocartesian` refine `Symmetric`; `Bistrong` refines `Strong` over a symmetric structure acting on itself; `Classical` refines `Restriction`; `Semilattice` refines `Monoid` |
| *is a*: a special case of something more general | `extends` with fixed arguments, or a view | an `Endofunctor` is a `Functor` from **K** to **K**; a `Bifunctor` is a `Functor` out of a product (`FromProduct`); a `Profunctor` is a `Bifunctor` out of **K₁**ᵒᵖ × **K₂**; an `Endoprofunctor` is a `Profunctor` from **K** to **K** |
| *dual*: the same structure on the opposite | an `Op` class | `Category.Op`; `Bifunctor.Op`; `Cartesian.Op` is `Cocartesian`; `Promonad.Op`; `Conway.OfElgot` |
| *induces*: a construction from one structure to another | an `open class` or a method | a category gives a promonad (`Promonad.Hom`); a monoidal category acts on itself (`Module.OfMonoidal`); a monad gives a promonad (`Kleisli`); a monoid gives a monad (`Writer`); a semilattice gives a preorder (`Preorder.of`) |
| *bridge*: two structures that define each other | `Of…` classes | `Traced.OfElgot` and `Elgot.OfTraced`; `Traced.OfConway` and `Conway.OfTraced` |
| *bundle*: structures used together | a class of `tracked` parameters | `Freyd(S)`; `parser.ParserAlgebra` |

## The map

```
Type ─ refines ─ Eq ─ induces ─ Observable ─ counterpart ─ Preorder            evidence and oracles

Category (Op, Product, Iso)                                                    𝒮 = Total, 𝒫 = Partial
└─ on ─ Functor ─ is a ─ Endofunctor ─ on ─ Monad ─ induces ─ Kleisli (a Promonad)
   │                                         ├─ on ─ RestrictionMonad ─ ClassicalMonad, ElgotMonad
   │                                         └─ transformers: Writer (from a Monoid), OptionT, StateT
   └─ Bifunctor (Op) ─ is a ─ Functor out of Category.Product
      ├─ on ─ Monoidal ─ refines ─ Symmetric ─ refines ─ Cartesian ⇄ Cocartesian (dual)
      │       ├─ on ─ Module (OfMonoidal)
      │       ├─ on ─ Closed (InternalHom, an Endoprofunctor)
      │       └─ on ─ Monoid ⇄ Comonoid (dual); Semilattice (on Cartesian) ─ induces ─ Preorder
      └─ Profunctor ─ is a ─ Bifunctor out of K₁ᵒᵖ × K₂
         ├─ on ─ Strong (+ Module) ─ refines ─ Bistrong (+ Symmetric, acting on itself)
         └─ is a ─ Endoprofunctor ─ refines ─ Promonad (Underlying, Op, Hom)
            ├─ on ─ Bistrong ─ bundle ─ Freyd
            │       └─ on ─ Traced ⇄ Conway (+ Cartesian), Elgot (+ Cocartesian)   bridges and duals
            ├─ on ─ Restriction ─ refines ─ Classical (+ Cocartesian)
            └─ on ─ Recursion
```

The concepts form three branches that meet in the parser: **tensors** (monoidal structure and the monoids in it),
**effects** (promonads and the structure on them), and **monads**, which are one way to build effects.

## An order that follows the dependencies

Each item needs only those before it:

1. `Type`, `Eq`
2. `Observable`
3. `Category` (with `Op`, `Product`, `Iso`), `Total`, `Partial`
4. `Functor`, `Endofunctor`
5. `Bifunctor`
6. `Monoidal`, `Symmetric`, `Module`
7. `Cartesian`, `Cocartesian`
8. `Profunctor`, `Endoprofunctor`, `Closed`
9. `Monoid`, `Semilattice`, `Comonoid`, then `Preorder`
10. `Promonad`
11. `Strong`, `Bistrong`, `Freyd`
12. `Restriction`, `Classical`
13. `Elgot`, `Conway`, `Traced`, `Recursion`
14. `Monad`, `Kleisli`
15. `RestrictionMonad`, `ClassicalMonad`, `ElgotMonad`; `Writer`, `OptionT`, `StateT`

`Total` and `Partial` are categories in item 3; their instances of later structures belong to the item of the
structure.
