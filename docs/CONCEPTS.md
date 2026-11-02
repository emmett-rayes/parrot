# How the structures relate

The structures of `parrot.category` are built from one another. This document maps how: what each structure is a
structure *on*, what it refines, what it is a special case of, what it is dual to, and what it induces. The tutorial's
concept index (Appendix E of [`TUTORIAL.md`](TUTORIAL.md)) says where each concept is introduced, and
[`DESIGN.md`](DESIGN.md) §4 at which level each one lives.

## Kinds of relation

| Relation | In the code | Examples |
| --- | --- | --- |
| *on*: structure on something else | a `tracked` parameter | `Monoidal(K, U, T)` on a category, a unit object and a bifunctor; `Module(K, M, T)` on a category and a monoidal category acting on it; `Strong(P, L1, L2)` on a profunctor and two modules; `Monad(F)` on an endofunctor; `Cone(D, X)` and `Cocone(D, X)` on a functor and an object, their diagram and apex; `Limits(J, C)` and `Colimits(J, C)` on a shape and a category; `Terminal(C, U)` and `Initial(C, U)` on a category and an object; `Product(C, U1, U2, U)` and `Coproduct(C, U1, U2, U)` on a category and three objects; `Restriction(P)` on a promonad |
| *refines*: more operations and laws | `extends`, forwarding the parameters | `Symmetric` refines `Monoidal`; `Cartesian` and `Cocartesian` refine `Symmetric`; `Bistrong` refines `Strong` over a symmetric structure acting on itself; `Classical` refines `Restriction`; `Semilattice` refines `Monoid`; `Limit` refines `Cone` and `Colimit` refines `Cocone`; `DiscreteLimits` and `DiscreteColimits` refine `Limits` and `Colimits` on a discrete shape; `Freyd` refines a category of arrows with a bistrong structure |
| *is a*: a special case of something more general | `extends` with fixed arguments, or a view | an `Endofunctor` is a `Functor` from **K** to **K**; a `Bifunctor` is a `Functor` out of a product (`FromProduct`); a `Profunctor` is a `Bifunctor` out of **K₁**ᵒᵖ × **K₂**; an `Endoprofunctor` is a `Profunctor` from **K** to **K**; `Option`'s monad is `OptionT` over `Monad.Identity`, `State[S]` is `StateT[S]` over it, and `Writer(W)` is `WriterT(W, Monad.Identity)` |
| *dual*: the same structure on the opposite | an `Op` class | `Category.Op`; `Bifunctor.Op`; `Cartesian.Op` is `Cocartesian`, from a terminal object and products as an initial object and coproducts (`Cartesian.OpInitial`, `Cartesian.OpCoproducts`), and `Cocartesian.Op` is `Cartesian`; `Promonad.Op`; `Bistrong.Op`; `Conway.OfElgot` |
| *induces*: a construction from one structure to another | an `open class` or a method | a category gives a promonad (`Promonad.Hom`); a promonad gives its category of arrows (`Promonad.Arrows`); a monoidal category acts on itself (`Module.OfMonoidal`); a symmetric monoidal category makes its hom bistrong (`Bistrong.Hom`); a monad gives a promonad (`Kleisli`); a monoid gives a monad (`Writer`); a semilattice gives a preorder (`Preorder.of`); a diagram into 𝒮 has a limit (`Total.LimitOf`) and a colimit (`Total.ColimitOf`), and one of a discrete shape a limit whose apex depends only on its objects (`Total.DiscreteLimitOf`) and a colimit, the sum of its points (`Total.DiscreteColimitOf`); discrete limits of shape **2** give products (`Products.FromLimits`), and discrete colimits coproducts (`Coproducts.FromColimits`) |
| *bridge*: two structures that define each other | `Of…` classes | `Traced.OfElgot` and `Elgot.OfTraced`; `Traced.OfConway` and `Conway.OfTraced`; a terminal object is a limit of the empty diagram (`Terminal.AsLimit`) and the other way round (`Terminal.FromLimit`), and so is a product, of a diagram of shape **2** (`Product.AsLimit`, `Product.FromLimit`); dually, an initial object and a coproduct are colimits (`Initial.AsColimit`, `Initial.FromColimit`, `Coproduct.AsColimit`, `Coproduct.FromColimit`) |
| *bundle*: structures used together | a class of `tracked` parameters | `parser.ParserAlgebra` |

## The map

```
Type                                                                           object evidence
Eq ─ induces ─ Observable ─ counterpart ─ Preorder                             equality and oracles

Category (Op, Product, Iso, Empty, Discrete2)                                  𝒮 = Total, 𝒫 = Partial
└─ on ─ Functor ─ is a ─ Endofunctor ─ on ─ Monad ─ induces ─ Kleisli (a Promonad)
   │                                         ├─ on ─ Monad.Restriction ─ Monad.Classical, Monad.Elgot
   │                                         ├─ transformers: OptionT, StateT, WriterT (+ Monoid)
   │                                         └─ Identity; over it, Option (OptionT), State (StateT), Writer (WriterT)
   ├─ on ─ Cone ─ refines ─ Limit ⇄ Terminal (of the empty diagram), Product (of a pair)
   │                        └─ Limits, of each shape ─ refines ─ DiscreteLimits ─ induces ─ Products (of shape 2)
   ├─ on ─ Cocone ─ refines ─ Colimit ⇄ Initial (of the empty diagram), Coproduct (of a pair)    duals
   │                          └─ Colimits, of each shape ─ refines ─ DiscreteColimits ─ induces ─ Coproducts
   └─ Bifunctor (Op) ─ is a ─ Functor out of Category.Product
      ├─ on ─ Monoidal ─ refines ─ Symmetric ─ refines ─ Cartesian ⇄ Cocartesian (dual)
      │       ├─ on ─ Module (OfMonoidal)
      │       ├─ on ─ Closed (InternalHom, an Endoprofunctor)
      │       └─ on ─ Monoid ⇄ Comonoid (dual); Semilattice (on Cartesian) ─ induces ─ Preorder
      └─ Profunctor ─ is a ─ Bifunctor out of K₁ᵒᵖ × K₂
         ├─ on ─ Strong (+ Module) ─ refines ─ Bistrong (+ Symmetric, acting on itself)
         └─ is a ─ Endoprofunctor ─ refines ─ Promonad (Op, Hom)
            ├─ induces ─ Arrows (a Category) ─ refines ─ Freyd (+ Bistrong)
            ├─ on ─ Bistrong (Op, Hom)
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
3. `Category` (with `Op`, `Product`, `Iso`, `Empty`, `Discrete2`), `Total`, `Partial`
4. `Functor`, `Endofunctor`, then `Cone`, `Limit`, `Limits`, `DiscreteLimits`, `Terminal`, `Product`, and dually
   `Cocone`, `Colimit`, `Colimits`, `DiscreteColimits`, `Initial`, `Coproduct`
5. `Bifunctor`
6. `Monoidal`, `Symmetric`, `Module`
7. `Cartesian`, `Cocartesian`
8. `Profunctor`, `Endoprofunctor`, `Closed`
9. `Monoid`, `Semilattice`, `Comonoid`, then `Preorder`
10. `Promonad`
11. `Strong`, `Bistrong`, `Freyd`
12. `Restriction`, `Classical`
13. `Elgot`, `Conway`, `Traced`, `Recursion`
14. `Monad` (with `Identity`), `Kleisli`
15. `Monad.Restriction`, `Monad.Classical`, `Monad.Elgot`; `OptionT`, `StateT`, `WriterT`; `Option`, `State`, `Writer`

`Total` and `Partial` are categories in item 3; their instances of later structures belong to the item of the
structure.
