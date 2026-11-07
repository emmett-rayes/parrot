# How the structures relate

The structures of `parrot.category` are built from one another. This document maps how: what each structure is a
structure *on*, what it refines, what it is a special case of, what it is dual to, and what it induces. The tutorial's
concept index (Appendix E of [`TUTORIAL.md`](TUTORIAL.md)) says where each concept is introduced, and
[`DESIGN.md`](DESIGN.md) §4 at which level each one lives.

## Kinds of relation

| Relation | In the code | Examples |
| --- | --- | --- |
| *on*: structure on something else | a `tracked` parameter | `Premonoidal(category, unit, tensor)` on a category, a unit object and a binoidal functor, and `Monoidal(category, unit, tensor)` on a category, a unit object and a bifunctor; `Module(monoidal, category, action)` on a monoidal category, a category it acts on and the action; `Strong(profunctor, monoidal, module1, module2)` on a profunctor, a monoidal category and two modules over it; `Monad(functor)` on an endofunctor; `Cone(diagram, apex)` and `Cocone(diagram, apex)` on a functor and an object, their diagram and apex; `Limits.InCategory(category)` and `Colimits.InCategory(category)` on a category, for a type of diagrams *D*; `Terminal(category)` and `Initial(category)` on a category, and `Product(category, first, second)` and `Coproduct(category, left, right)` on a category and two objects, each an object of the category itself; `Restriction(category)` on a category; `Traced(premonoidal)` on a symmetric premonoidal category; `Freyd(strong)`, `Elgot(strong)` and `Conway(strong)` on a bistrong promonad, a `StrongPromonad`; `Recursion(promonad)` on a promonad |
| *refines*: more operations and laws | `extends`, forwarding the parameters, or a trait with the refined structure as its self-type | `Bifunctor` refines `BinoidalFunctor`; `Products` and `Coproducts` refine `Endobifunctor`; `Monoidal` and the trait `SymmetricPremonoidal` refine `Premonoidal`, and `Symmetric` refines both; `Cartesian` refines `Symmetric` with a terminal unit and products as its tensor, and `Cocartesian` with an initial unit and coproducts; `Bistrong` refines `Strong` over a symmetric structure acting on itself; `Classical` refines `Restriction`; `Semilattice` refines `Monoid`; `Limit` refines `Cone` and `Colimit` refines `Cocone`; `Limits.DiscreteInCategory` and `Colimits.DiscreteInCategory` refine `Limits.InCategory` and `Colimits.InCategory` for the diagrams of a discrete shape; `Freyd` refines `Premonoidal` on the arrows of its promonad and mixes in `SymmetricPremonoidal` |
| *is a*: a special case of something more general | `extends` with fixed arguments, or a view | an `Endofunctor` is a `Functor` from **C** to **C**; a `Bifunctor` is a `Functor` out of a product (`FromProduct`); an `Endobifunctor` is a `Bifunctor` from **C** × **C** to **C**; a `Profunctor` is a `Bifunctor` out of **C₁**ᵒᵖ × **C₂**; an `Endoprofunctor` is a `Profunctor` from **C** to **C**; `Option`'s monad is `OptionT` over `Monad.Identity`, `State[S]` is `StateT[S]` over it, and `Writer(monoid)` is `WriterT(monoid, Monad.Identity)`; a `Terminal`, an `Initial`, a `Product`, a `Coproduct`, a `Monoid` and a `Comonoid` are each a `Category.Object` of their category |
| *dual*: the same structure on the opposite | an `Op` class | `Category.Op`; `Bifunctor.Op` and `Endobifunctor.Op`; `Terminal.Op` is `Initial` and `Initial.Op` is `Terminal`; `Product.Op` is `Coproduct` and `Coproduct.Op` is `Product`; `Products.Op` is `Coproducts` and `Coproducts.Op` is `Products`, each the view `op` of its structure; `Symmetric.Op`; `Cartesian.Op` is `Cocartesian`, from the views `op` of its unit and tensor, and `Cocartesian.Op` is `Cartesian`; `Promonad.Op`; `Bistrong.Op`; `Conway.OfElgot` and `Elgot.OfConway`, on `Bistrong.Op` |
| *induces*: a construction from one structure to another | an `open class` or a method | a category gives a promonad (`Promonad.Hom`); a promonad gives its category of arrows (`Promonad.Arrows`) and the functor of its pure arrows into it (`Promonad.Pure`); a monoidal category acts on itself (`Module.OfMonoidal`); a symmetric monoidal category makes its hom bistrong (`Bistrong.Hom`); a bistrong promonad gives a Freyd category (`Freyd`), whose tensor has the strengths as its maps (`Freyd.Tensor`); a closed structure makes its internal hom an endoprofunctor (`Closed.InternalHom`); a cartesian category makes every object a comonoid (`Cartesian.comonoid`), and a cocartesian category a monoid (`Cocartesian.monoid`); a monad gives a promonad (`Kleisli`), strong for products or coproducts (`Kleisli.ProductStrength`, `Kleisli.CoproductStrength`), with the restriction, classical and iteration structures of the monad (`Kleisli.RestrictionOf`, `Kleisli.ClassicalOf`, `Kleisli.ElgotOf`); `OptionT` gives a classical monad (`OptionT.ClassicalOf`), and `StateT` over a classical monad gives one too (`StateT.ClassicalOf`) and, with a `Measure`, guarded iteration and recursion (`StateT.GuardedIteration`, `StateT.GuardedRecursion`); a monoid gives a monad (`Writer`); a semilattice gives a preorder (`Preorder.of`); a diagram into 𝒮 has a limit (`Total.LimitOf`) and a colimit (`Total.ColimitOf`), and one of a discrete shape a limit whose apex depends only on its objects (`Total.DiscreteLimitOf`) and a colimit, the sum of its points (`Total.DiscreteColimitOf`); discrete limits of shape **2** give products (`Products.FromLimits`), and discrete colimits coproducts (`Coproducts.FromColimits`) |
| *bridge*: two structures that define each other | `Of…` classes | `Traced.OfElgot` and `Elgot.OfTraced`; `Traced.OfConway` and `Conway.OfTraced`, through the trace on the Freyd category of the strength; a terminal object is a limit of the empty diagram (`Terminal.AsLimit`) and the other way round (`Terminal.FromLimit`), and so is a product, of a diagram of shape **2** (`Product.AsLimit`, `Product.FromLimit`); dually, an initial object and a coproduct are colimits (`Initial.AsColimit`, `Initial.FromColimit`, `Coproduct.AsColimit`, `Coproduct.FromColimit`) |
| *bundle*: structures used together | a class of `tracked` parameters | `parser.ParserAlgebra` |

## The map

```
Type                                                                           object evidence
Eq ─ induces ─ Observable ─ counterpart ─ Preorder                             equality and oracles

Category (Op, Product, Iso, Object, Empty, Discrete2)                          𝒮 = Total, 𝒫 = Partial
└─ on ─ Functor ─ is a ─ Endofunctor ─ on ─ Monad ─ induces ─ Kleisli (a Promonad)
   │                                         ├─ on ─ Monad.Restriction ─ refines ─ Monad.Classical
   │                                         ├─ on ─ Monad.Elgot
   │                                         ├─ transformers: OptionT, StateT, WriterT (+ Monoid)
   │                                         │  └─ StateT (+ Measure) ─ induces ─ GuardedIteration, GuardedRecursion
   │                                         └─ Identity; over it, Option (OptionT), State (StateT), Writer (WriterT)
   ├─ on ─ Cone ─ refines ─ Limit ⇄ Terminal (of the empty diagram), Product (of a pair)
   │                        └─ Limits.InCategory ─ refines ─ Limits.DiscreteInCategory ─ induces ─ Products (of shape 2)
   ├─ on ─ Cocone ─ refines ─ Colimit ⇄ Initial (of the empty diagram), Coproduct (of a pair)    duals
   │                          └─ Colimits.InCategory ─ refines ─ Colimits.DiscreteInCategory ─ induces ─ Coproducts
   ├─ on ─ Restriction ─ refines ─ Classical
   └─ BinoidalFunctor ─ refines ─ Bifunctor (Op) ─ is a ─ Functor out of Category.Product
      ├─ on ─ Premonoidal ─ refines ─ SymmetricPremonoidal (a trait) ─ on ─ Traced
      │       └─ refines ─ Monoidal ─ refines ─ Symmetric (Op, + the trait) ─ refines ─ Cartesian ⇄ Cocartesian
      │                    ├─ on ─ Module (OfMonoidal)
      │                    ├─ on ─ Closed (InternalHom, an Endoprofunctor)
      │                    └─ on ─ Monoid ⇄ Comonoid (dual); Semilattice (on Cartesian) ─ induces ─ Preorder
      ├─ is a ─ Endobifunctor (Op) ─ refines ─ Products, Coproducts
      └─ Profunctor ─ is a ─ Bifunctor out of C₁ᵒᵖ × C₂
         ├─ on ─ Strong (+ Monoidal, Module) ─ refines ─ Bistrong (+ Symmetric, acting on itself)
         └─ is a ─ Endoprofunctor ─ refines ─ Promonad (Op, Hom)
            ├─ induces ─ Arrows (a Category)
            ├─ induces ─ Pure (a Functor into Arrows)
            ├─ on ─ Bistrong (Op, Hom), a StrongPromonad
            │       ├─ on ─ Freyd (Tensor, a BinoidalFunctor) ─ refines ─ Premonoidal on Arrows, + SymmetricPremonoidal
            │       └─ on ─ Conway (+ Cartesian), Elgot (+ Cocartesian) ⇄ Traced on Freyd   bridges and duals
            └─ on ─ Recursion
```

The concepts form three branches that meet in the parser: **tensors** (monoidal structure and the monoids in it),
**effects** (promonads and the structure on them), and **monads**, which are one way to build effects.

## An order that follows the dependencies

Each item needs only those before it:

1. `Type`, `Eq`
2. `Observable`
3. `Category` (with `Op`, `Product`, `Iso`, `Object`, `Empty`, `Discrete2`), `Total`, `Partial`
4. `Functor`, `Endofunctor`, then `Cone`, `Limit` (with `Limits`), `Terminal`, `Product`, and dually `Cocone`,
   `Colimit` (with `Colimits`), `Initial`, `Coproduct`
5. `BinoidalFunctor`, `Bifunctor`, `Endobifunctor`, then `Products`, `Coproducts`
6. `Premonoidal`, `SymmetricPremonoidal`, `Monoidal`, `Symmetric`, `Module`
7. `Cartesian`, `Cocartesian`
8. `Profunctor`, `Endoprofunctor`, `Closed`
9. `Monoid`, `Semilattice`, `Comonoid`, then `Preorder`
10. `Promonad`
11. `Strong`, `Bistrong`, `StrongPromonad`, `Freyd`
12. `Restriction`, `Classical`
13. `Elgot`, `Conway`, `Traced`, `Recursion`
14. `Monad` (with `Identity`), `Kleisli`
15. `Monad.Restriction`, `Monad.Classical`, `Monad.Elgot` (with `Kleisli.RestrictionOf`, `Kleisli.ClassicalOf`,
    `Kleisli.ElgotOf`); `OptionT`, `StateT`, `WriterT`; `Option`, `State`, `Writer`; `Measure`,
    `StateT.GuardedIteration`, `StateT.GuardedRecursion`

`Total` and `Partial` are categories in item 3; their instances of later structures belong to the item of the
structure.
