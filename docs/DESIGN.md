# Design rationale

The design of the library: the categorical structures of `parrot.category` and the parser of `parrot.parser`. Each
decision states what was chosen and why; the alternatives that were rejected follow it. The rules that follow from the
decisions are in [`CLAUDE.md`](../CLAUDE.md), and the mathematics is explained in [`TUTORIAL.md`](TUTORIAL.md). Treat
the decisions as settled, and reopen one only with a new argument.

## 1. Principles

- **Faithful:** each construct is the mathematical notion, not an approximation.
- **General** where the mathematics allows it, and **symmetric**: no unexplained asymmetries across the hierarchy.
- **Each notion defined once:** no parallel hierarchies, and derived structure wherever possible.
- **`extends` only refines a notion;** structure *on* something takes it as a parameter.
- **𝒮 is the ground:** everything lives inside the category of total programs.
- **Usable:** plain syntax, and designs that compile without casts.

The category library stands on its own; the parser is its first and most important client.

## 2. Two categories of programs

- **𝒮 and 𝒫.** 𝒮 (`Total`) has the pure, total functions `A -> B`; 𝒫 (`Partial`, an opaque alias of `A -> B`) has the
  pure programs that may not terminate. Purity (`->` versus `=>`) and totality (𝒮 versus 𝒫) are separate axes:
  capture checking checks purity, while totality is a promise. `=>` functions have no category instances.
- **Unguarded recursion and loops live in 𝒫, guarded ones in 𝒮.** A category with products, function types, an initial
  object and a fixed point for every endomorphism has an arrow 1 → 0, the fixed point of the identity on 0, and then
  collapses (Huwig and Poigné), so 𝒮 cannot have general recursion or iteration. 𝒫 is a restriction category whose
  total arrows are exactly 𝒮 (Cockett and Lack); its pairs are restriction products, not products.
- **One promise of totality.** `Partial(f)` is a program, total or not, and `Partial.fromTotal(f)` includes 𝒮 in 𝒫;
  `Partial.assumeTotal(p)` is the library's single, greppable promise that a program of 𝒫 is total.

Rejected:
- lazy pairs as the product: isomorphic to ordinary pairs in 𝒮, and not a product in 𝒫, where a program can tell a
  diverging pair from the pair of its diverging components;
- a wrapper type for pure functions, which capture checking makes unnecessary.

## 3. The encoding

- **Bases are `tracked` term parameters** (`Strong(profunctor, monoidal, module1, module2)`, `Promonad(category)`,
  `Monad(functor)`). A term parameter is a stable path, so its type members can be named and imported, and `tracked`
  keeps its singleton type in the instance's type, so `Kleisli.OptionKleisli.category` is known to be `Total` without
  casts.
- **What a structure is on is a parameter; what it adds is a member.** `Monoidal(category, unit, tensor)` is on a
  category, a unit object and a tensor, an `Endobifunctor`, and names their types `I = unit.A` and `Tensor = tensor.F`,
  which `tracked` makes known to clients (`Total.Products.I` is `Unit`). The unitors, the associator and the braiding
  are members, because refinements derive them (`Cartesian`); so is the internal hom, which is what `Closed` adds: ⊗
  determines it up to isomorphism, and evaluation and currying determine its action on morphisms (`Closed.InternalHom`).
- **Evidence that chooses an object is a value parameter** (the unit of `Monoidal`, the factors and product of
  `Product`, the apex of `Cone`). 𝒮 has two units and two tensors, so implicit search cannot choose them (for a `using`
  parameter it chose `Type.TIsType[Any]`), and `deferred` givens exist only in traits; that makes it a value. It is a
  parameter because a structure is on the objects it is about: a cone is a natural transformation from the constant
  functor at its apex to its diagram, so it is on both, and a limit passes the apex it chooses to its parent.
- **Structures offer evidence as values, and every given is private** to the class that uses it: a bifunctor has
  `objects`, an object its `evidence`, a cone its `apex`, and a class that needs a given declares one from them
  (`private given TensorIsObj: [A: Obj, B: Obj] => ((A * B) is Obj) = tensor.objects[A, B]`), refinements included. The
  only public givens are instances of type classes, next to their type class (`Type.TIsType`, `Eq`, `Observable`).
- **Every object a structure chooses or is on is a structure,** `Category.Object(category)`, written `category.Object`:
  one encoding for all of them, which a refinement can ask more of: `Monoidal(category, unit, tensor)` is on an
  `Object`, and `Cartesian` refines it to a `Terminal`, an `Object` with `discard`, as it refines the endobifunctor
  `tensor` to `Products`. An object has its own carrier, `Self`, and the `evidence` that it is an object,
  `Self is category.Obj`, so `A is category.Object` is the object *A*, which `category.Object[A]` builds from a context
  bound, and no structure takes bare evidence: a terminal object defines its carrier and evidence
  (`Total.UnitIsTerminal` is a `Unit is Terminal`).
- **Structures are abstract classes,** because a refinement passes arguments to its parent (`Promonad(category)` extends
  `Endoprofunctor(category, Total)`), which a trait cannot. Type classes without parameters that are not structures
  (`Category.Type`, `Eq`, `Observable`, `Preorder`, `Measure`) are traits.
- **`Self` only when the structure has its own carrier** (a category's morphisms, a functor's object map, a monoid's
  object). Structures *on* something (`Monoidal`, `Module`, `Strong`, `Restriction`, the trace grid, `Monad`) are
  named, not found by carrier: 𝒮 carries both products and coproducts, and nothing about the carrier tells them apart.
- **Combinations are bundles, not inheritance.** A class extending a product and a coproduct structure would inherit two
  `Tensor`s, two `I`s and two `braid`s, so `ParserAlgebra(…)` takes its structures as parameters. A structure that is
  another with more operations extends it: `Freyd(promonad, strong)` extends the category of arrows
  `Promonad.Arrows(promonad)`.
- **A special case with an operation of its own is a structure with a view** to the general one and a construction
  back (`Terminal.asLimit` and `Terminal.FromLimit`, `Bifunctor.functor`, `Promonad.arrows`): an instance can override
  the operation with a better implementation, and the laws of both structures still check it. An alias (`Monad.On`,
  `Limit.Of`) only names a refinement.
- **Refinements go through one alias per class, for its base:** the parameter that the first sentence of the class's
  doc relates it to, whose preposition names the alias (`Endofunctor.On`, `Limit.Of`, `Monoid.In`, `Cone.Over`,
  `Cocone.Under` and `Into` for the target of a class documented as an arrow, `Functor.Into`), with what the doc
  names as its argument (`Monad.On[K]` refines the category of the endofunctor). The base is refined only through its
  alias and every other member inline after it, so each parameter has one spelling whatever the names at the use, and
  a refinement of the base is never cyclic, as `Endobifunctor { val category: category.type }` is, where `category` is
  the refinement's own member. A class with type parameters of its own (`StateT[S]`) has no alias, which would take
  them by position. A type member that clients bound has an alias beside the class (`Limits.OfDiagram[T]` is
  `InCategory { type D >: T[category.type] }`), whose argument is indexed by the category so that the bound can name
  the refined structure's own `category`.
- **Objects are types with evidence.** A category declares `type Obj <: Type`, where `Type` is `Category.Type`, object
  evidence and nothing else. Evidence travels only through context bounds, which come after the value parameters, so
  that infix code infers its types. Evidence classes such as `Pair`, the objects of `Category.Product`, extend `Type`,
  so evidence search is sound but not canonical. Type classes of data (`Eq`, `Observable`, `Preorder`) do not extend
  `Type`, since importing their givens would change what answers `A is Type`; a category of the types with an
  equality takes an evidence class that carries an `Eq`.
- **Products of categories use match types.** The objects of `Category.Product(first, second)` are pair types, and a
  morphism type computed from two object types can take them apart only with a match type (`Fst[(A1, A2)] = A1`):
  evidence is a value and cannot index a type, and projecting a type member of an abstract type is unsound. The object
  evidence speaks about `Fst[X]` and `Snd[X]` directly, so generic code never needs a match type to reduce. A bifunctor
  keeps its own two-parameter carrier and is a functor out of the product through the view `Bifunctor.functor`, whose
  functor laws are its laws.
- **A monad is structure on an endofunctor,** `Monad(functor)`, with `unit` and `flatten` primitive: the monoid
  presentation, so that `Monad` and `Monoid` have the same shape, with `bind` derived. Monads are refined through their
  functor (`Monad.On[Total.type]`), since only that keeps the chain of singleton types that path-dependent code needs.
  The structures on a monad whose laws are those of the Kleisli structures they induce (`Monad.Restriction`,
  `Monad.Classical`, `Monad.Elgot`) live in its companion. Plain monads are transformers over the identity
  (`Monad.OptionIsMonad` is `OptionT(Monad.Identity)`), so that each effect is defined once.
- **Names follow the mathematics:** short carrier aliases (`Hom`/`-->`, `F`, `P`, `M`, `C`), role names for the arrows
  of other categories (`->>`, `==>`, `~~>`) beside the concrete `->` of 𝒮 and `~>` of 𝒫, and infix objects (`*`, `+`,
  `` `^` ``, `<->`). No operator reuses a name that a type already has: the preorder is `?<`, since `Int`'s own `<=`
  would shadow `<=`.
- **Parameters are named by their role,** in one lowercase word (`source` and `target`, `category`, `unit` and `tensor`,
  `diagram` and `apex`, `strong`), indexed when a structure has two of a kind (`source1`, `source2`); the scaladoc
  keeps the mathematical letters (**C**, *F*). Clients reach a structure through paths of parameters, and a path of
  role names says what each link is: `strong.profunctor.category` is the category of the strong profunctor.
- **One operator per operation, and operators are syntax.** The same operator of two structures is an overload that
  Scala resolves by the type of the arrow, so a category and a promonad both compose with `>>>`; where one value is an
  arrow of both (a Kleisli arrow `A -> M[B]` on 𝒮), Scala reports an ambiguity or rejects the argument, never a wrong
  composition, since both readings type-check only if *B* = *M*(*B*). Each operator forwards its arguments in order to
  a named method (`p >>> q` is `andThen(p, q)`), so every operation has a name that docs, laws and searches can use.

Rejected:
- bases as type parameters, which cannot be imported from and need `ValueOf` and casts to recover the base values;
- structures as traits whose bases are abstract `tracked val` members, which instances define in their bodies:
  refinements would narrow their parent's members instead of restating and forwarding them. A trait's initializer runs
  before the instance's body, so a refinement that stores a member computed from another (the source and target of
  `Endofunctor`, the modules of `Bistrong`) stores `null`. Such a member must be an export alias, which the compiler
  checks to be stable and evaluates on access, since a lazy val cannot implement an abstract val and an abstract lazy
  val is not a path. Exports satisfy the initialization checkers, but an instance must then annotate each member whose
  type depends on another with its singleton type (`val monoidal: Products.type = Products`): the inferred type fails
  the override check, and any other annotation loses the refinement;
- parameters named by single letters, after the mathematics (`K`, `P`, `M`): a letter names different things in
  different structures (`C` is a category, a Conway operator or a closed structure) and collides with the carrier
  aliases (`M.M`, `P.P`). Role names collide in refinements instead (`Product { val category: category.type }`), which
  the aliases that refine a structure avoid (`Product.Of[category.type]`);
- refinements written inline unless they are cyclic, with an alias only where a role name collides: the spelling of a
  refinement then depends on the names at its use;
- several aliases per class, chosen at each use: a parameter is then spelled by its alias alone and inline beside
  another, since aliases combine only by intersection, which breaks singleton chains, or by taking the type they
  refine as an argument;
- an alias for every refinement, which is positional and drops the role names that say what each member is;
- one name for every alias, which reads wrongly for objects, limits and cones (`Terminal.On`, `Cone.On`);
- bare evidence for every object (`unit: category.Obj`), with a terminal object as structure on its apex: `Obj` is an
  abstract type, which no class can extend, so `Cartesian` would ask for a terminal unit through a parameter of another
  name (`terminal`, passing its apex as the unit) while it refines its tensor in place, and a terminal object would not
  be an object;
- bare evidence for the objects that no refinement asks more of, such as the factors of a product or the apex of a
  cone: shorter, but a second encoding of one concept;
- an object that takes its evidence as a parameter and reads its type from it (`A = evidence.Self`): naming an object
  by its type then refines its evidence (`{ val evidence: X is Obj }`), which needs an alias declared elsewhere, since
  inside a refinement of `Object` the name `A` is its member; and an object with its type as a type parameter, which no
  class can extend at a type that depends on its own parameters (the terminal object of a limit, at the limit's apex);
- `Object` as a class nested in `Category`: a structure that extends it through a parameter (`category.Object`) is not
  an object of the argument (`Total.Object`), so a terminal object could not be passed as a unit;
- object evidence as a type constructor (`type Obj[_]`, evidence `Obj[A]`), which would make the evidence of **2** a
  plain GADT but has no `Self`: every parameter that chooses an object would need a wrapper pairing a type with its
  evidence;
- `Bifunctor` extending `Functor`, which puts match types into every instance's signatures, and a separate class for
  categories whose objects are pairs of types, which duplicates `Category`;
- operators with logic of their own, which hide an operation;
- givens that structures offer to their clients: a given member is found through the prefix of every type that
  mentions its structure, so two structures offering the same evidence, a monoidal structure and its tensor, are
  ambiguous for every client;
- `protected` givens shared with refinements: they are in scope in instances too, where a given defined from a member
  that the instance implements by implicit search makes that member call itself.

## 4. The structures

Each structure sits at the lowest level where its laws can be stated.

| Row | Over products | Over coproducts | Level |
| --- | --- | --- | --- |
| strength | `Bistrong` (⊗ = ×) | `Bistrong` (⊗ = +), also called choice | `Strong`: a profunctor over left modules (a Tambara module); `Bistrong`: over a symmetric **K** acting on itself |
| trace | `Traced` (×) | `Traced` (+) | a bistrong promonad: superposing needs composition and strength |
| fixed point | `Conway` | `Elgot`, which is `Conway` on *P*ᵒᵖ | a bistrong promonad |

- **Strength over left modules.** `Strong(profunctor, monoidal, module1, module2)` is a profunctor *P*: **K₁**ᵒᵖ ×
  **K₂** → **V** with left actions (`Module`) of one monoidal **M** on **K₁** and **K₂**; its primitive is the left
  strength *τ*: *P*(*A*,*B*) → *P*(*C* ⊘₁ *A*,*C* ⊘₂ *B*), `left`, as in the literature (Pastro and Street's Tambara
  modules; Moggi's strength is a left strength). The general definition costs nothing, since every instance is the
  self-action. *τ* is an arrow of **V**, like the action *P*(*f*,*g*), not a function on arrows of *P*: a strength needs
  nothing of **V**, and like the action it has no congruence law.
  `Bistrong(profunctor, monoidal)`, for a symmetric **M** acting on itself, is the only case with a right action too: it
  adds the right strength *τ*′, `right`, and the law that the two commute (`compatibility`). *τ*′ defaults to
  *P*(*β*,*β*) ∘ *τ* and may be overridden, as `StrictParser` does to build `Zip(p, Success())` directly. `Strong` and
  `Traced` are defined once, parameterized by the monoidal structure.
- **A Freyd category is a category:** `Freyd(promonad, strong)` extends `Promonad.Arrows(promonad)`, the category of
  arrows of the promonad, with `first`, `second`, `parallel` and the laws that connect them to the strength. It names
  the strengths after the component an arrow runs on, `first` = *τ*′ and `second` = *τ*, so that the laws of Freyd
  categories and the grid read as usual. It takes the promonad as well as the strength, so that its signature names the
  promonad whose arrows it has.
- **Traces and fixed points.** The trace laws restrict sliding and superposing to pure arrows, which are central
  (traced *premonoidal* categories). The product row has no useful total instance in a strict language: computing
  ⟨*id*,*p*†⟩ ⨾ *p* requires *p*† first. Its instances exist by duality, on 𝒫ᵒᵖ, and the bridges (`OfElgot`,
  `OfConway`, `OfTraced`) are tested in both rows.
- **Recursion at the types of arrows,** `Recursion`, is a fixed point in 𝒮 at the type *P*(*A*,*B*), not an operation
  of the category of arrows: a grammar rule refers to itself as a value. In 𝒫 it ties the η-expanded knot; in 𝒮 it is
  guarded. Mutual recursion is a fixed point of a family of arrows, `fixFamily`, with one knot per arrow.
- **Guarded iteration and recursion** (`StateT.GuardedIteration`, `StateT.GuardedRecursion`) are total by construction
  and lawful on guarded arguments, after Goncharov and Schröder; yanking fails for the guarded trace, which is a
  counterexample test.
- **Restriction.** `Restriction` has R1–R4; `Classical` adds the restriction zero, complements and override ⊳ with the
  axioms of Lemay and Nester, which make PEG ordered choice a theorem rather than an invention. Postcomposition does
  not distribute over ⊳; precomposition does.
- **Comonoids** are the dual of monoids. Every object of a cartesian category is a comonoid in exactly one way; pairs in
  𝒫 have comonoids that programs do not preserve, which by Fox's theorem is why they are not products.
- **Limits.** `Limit(diagram, apex)` is a cone over a diagram *D* with apex *X* (`Cone`) through which every cone
  factors, and `Limits.InCategory(category)` gives one for every diagram of its type member `D`, a type of diagrams into
  **C**. The limits of more diagrams serve for fewer, so a client asks for the diagrams it needs as a lower bound on
  `D`, `Limits.OfDiagram[T]` for a type *T*[*K*] of diagrams into *K*: `Terminal(limits)` takes
  `Limits.OfDiagram[EmptyDiagram.Into]`. 𝒮 has all of them by one construction, `Total.LimitOf`, which `Total.Limits`
  gives for every diagram: the product of the components is a polymorphic function type, since the objects are types,
  and the equalizer of the natural families is made by abstraction. Points are private to the construction, a class
  indexed by the diagram (`LimitOf.Point`), and only the factorization builds them, from the legs of a cone, so they are
  natural as long as the cones are lawful; to clients, who see points only through the legs, the abstract type is the
  limit.
- **Limits of a discrete shape have a type of apexes.** `Limits.DiscreteInCategory(category)` refines `InCategory`,
  narrowing `D` to the diagrams of a shape whose only morphisms are identities, stated as a bound on their source (`Self
  <: =:=`, which **2** and **0** satisfy), and gives the apex of each limit as a type function `Apex[O, D]` of the
  objects *O* of the shape and the object map *D* of the diagram; clients ask through `Limits.OfDiscreteDiagram[T]`. A
  functor preserves identities, so a discrete shape is determined by its objects and a diagram of it by its object map,
  and the apex can be too; for any other shape it cannot, since the limit depends on the morphisms. In 𝒮
  (`Total.DiscreteLimits`) every family of points is natural, so the apex is the type of all families, without
  abstraction.
- **Colimits are the dual, stated directly** so that their legs and factorizations are morphisms of **C**:
  `Cocone(diagram, apex)`, `Colimit(diagram, apex)` with `factor` out of its apex, `Colimits.InCategory` and
  `Colimits.DiscreteInCategory` with the apex `Apex[O, D]`, asked for through `Colimits.OfDiagram` and
  `Colimits.OfDiscreteDiagram`. 𝒮 has all of them by the dual construction, `Total.ColimitOf` (`Total.Colimits`): the
  sum of the points is an existential type, `Total.Sum[O, F]`, a point of *F*[*A*] together with the evidence for its
  object *A*, a type that it hides, and the coequalizer that glues *x* to *D*(*f*)(*x*) is made by abstraction. Points
  are private to the construction (`ColimitOf.Point`) and only the factorization reads them, through the legs of a
  cocone, so glued points are indistinguishable as long as the cocones are lawful; to clients, the abstract type is the
  colimit. In a discrete diagram no two points are glued, so the colimit is the sum itself (`Total.DiscreteColimits`),
  and the factorization applies the leg at the object of a point.
- **Terminal objects and products are structures with views** (§3). `Terminal(category)` is an object with `discard`
  (!); `Product(category, first, second, apex)` has `fst`, `snd` and `pair`. Each is a limit through its view
  `asLimit`, of the empty diagram and of a diagram of shape **2** (`Category.Discrete2`), and `FromLimit` builds each
  from a limit. `Products(category)`, the binary products of **C**, is a bifunctor with a `Product` on every image,
  `product[A, B]` on *F*[*A*,*B*], whose laws are its laws, and `bimap` defaults to ⟨*f* ∘ *π*₁,*g* ∘ *π*₂⟩.
  `Products(limits)` (`Products.FromLimits`) builds them from discrete limits of shape **2**, with the apexes
  Apex[**2**,(*A*,*B*)] as tensor, as `Terminal(limits)` builds a terminal object; an instance with a tensor of its own
  implements one `Product` per pair of objects (`Total.Tuple2IsProduct[A, B]`). Dually, `Initial(category)` has `absurd`
  (¡) and `Coproduct(category, left, right, apex)` has `inl`, `inr` and `copair`, each a colimit through its view
  `asColimit` and built from one by `FromColimit`, and `Coproducts(category)` has a `Coproduct` on every image,
  `coproduct[A, B]`, with `Coproducts(colimits)` from discrete colimits.
- **A cartesian structure is a terminal object and products,** `Cartesian(category, unit, tensor)`, whose unit is a
  `Terminal` and whose tensor is `Products`: the universal properties are stated once, in its parameters, and
  `Cartesian` derives the unitors, the associator and the braiding from them, with laws that check an instance
  overriding them against the projections. Its `fst`, `snd` and `pair` are those of `tensor.product`, named once for the
  code that works in a cartesian category. Dually, `Cocartesian(category, unit, tensor)` takes an `Initial` unit and
  `Coproducts`, names `inl`, `inr` and `copair`, and checks the unitors, the associator and the braiding against the
  injections.
- **2 tells its objects apart by a GADT carried by the evidence:** `Disc2.index` is an `Index[A]`, and matching on its
  cases `Zero` and `One` refines `A`. A match on the evidence itself would not, because Scala derives GADT constraints
  from type parameters, not from the `Self` of `A is Disc2`; nor can the evidence be the GADT, because a context bound
  needs an abstract `Self`.
- **One level of enrichment.** A category with a semantic equality on its homs and congruence laws is enrichment over
  setoids, and parsers with a preorder on their homs are enrichment over preorders; both are stated directly, without
  a hierarchy of enriched categories.

Rejected:
- strength as a refinement of `Monoidal` (`first = p *** id`), which is vacuous: every law follows from
  bifunctoriality;
- naming the primitive strength `first`: with a left action it runs an arrow on the *second* component;
- `Bistrong` over two arbitrary left modules: a left module has no right action, so it would need right modules or
  bimodules, which have no client;
- `Bistrong` constraining the profunctor towards the monoidal structure
  (`Profunctor { val domain: monoidal.category.type; … }`): for a promonad, nothing makes its own **K** equal to
  **M**.**K**, so the constraint refines **M** instead;
- separate duals over products and coproducts, where one `Bistrong.Op(strong, strong.monoidal.op)` serves both, its
  braiding unchecked;
- solving mutual recursion one arrow at a time (Bekić), which applies the definition exponentially often in the number
  of arrows and cannot share a guard between separately tied knots;
- a terminal object as an alias of a limit of the empty diagram, which leaves it no operation to override;
- `Cartesian` with projections, pairing and ! of its own, which restates the operations and laws of `Terminal` and
  `Products`, and `Cocartesian` with injections, copairing and ¡ of its own;
- colimits as limits in **C**ᵒᵖ, whose legs and factorizations are morphisms of **C**ᵒᵖ that every client would have
  to reverse;
- products from any limits of shape **2** (`Limits.OfDiagram[Discrete2Diagram.Into]`): the apex of a limit is a type of
  each limit, not a type constructor, so it cannot be the tensor that monoidal signatures apply to two types;
  `DiscreteInCategory` gives the apex as a type function instead;
- the apex of a cone as a type member with evidence, which an implementation defines in its body: it lets a limit of 𝒮
  nest its type of points in itself, but every other cone restates a parameter as two members, and the apex of a cone is
  what it is on, like the object of a terminal object;
- limits of a shape, a structure on a shape **J** and a category **C** with a limit of every diagram **J** → **C**:
  clients need the limits of one kind of diagram, the empty one or the pairs of objects, and 𝒮 has the limits of every
  diagram, of any shape;
- limits of every diagram, without a type of diagrams: `DiscreteInCategory` takes fewer diagrams, so its `limit` could
  not override the general one, whose parameter it would narrow, and `Terminal(limits)` would need every limit;
- the type of diagrams as a type parameter, contravariant and indexed by the category (`InCategory[-D[K <: Category]]`):
  the type parameters of a class cannot mention its parameters, so every instance and client passes a type lambda,
  where a type member names `category` and a lower bound at the use gives the same variance;
- a type function of the object map as the apex of every `InCategory`: the limit of a shape with morphisms depends on
  them, and in 𝒮 a shared type of points would let a point natural for one diagram reach the legs of another with the
  same objects;
- `fst`, `snd` and `pair` on `Products`, as primitives with `product` a view assembled from them or as forwarders to
  `product`: they restate at every two objects what a `Product` is, and their clients work in a `Cartesian`;
- a Church-encoded case analysis on the objects of **2** (`fold[R[_]]`), which needs a type lambda at every use;
- applied constructor types (`Functor(J, C)` as a type), which avoid the refinement shadowing that `Limit.Of` and
  `this`-qualified paths work around: scalac accepts them, but Scalameta, and so Pants, does not.

## 5. Laws, and how they are checked

- **`Eq` is semantic equality on data,** with equivalence laws, and every operation that consumes it has a congruence
  law. Functions have no `Eq`. An `Eq` is stated per type (`Eq.structural`), never derived from `CanEqual`, which only
  permits `==`: that would make reference identity the equality of plain classes, and give `Double` an equality that
  is not reflexive.
- **`Observable` is the law-checking oracle:** finitely many observations ending in data compared with `Eq`,
  deterministic, pure and sound for refutation. Sampled agreement is an equivalence but not a congruence, so
  congruence laws take *variants*, values equal by construction. `Preorder` is its counterpart for inequations. Both
  have laws of their own, tested for every observation the law tests use: agreement is an equivalence and an order is
  a preorder; both are *sound*, since variants agree and are ordered both ways; and an order contains agreement, for
  an `Observable` that makes the same observations. That congruence fails is a counterexample test.
- **Randomness lives only in generators, and sample points are generated per property.** Arrows come from sharp
  generators (failure, partiality, consumption); conditional laws use targeted generators instead of `==>`.
- **Iteration and fixed-point operators satisfy dinaturality for all arrows,** effectful ones included.
- **One generic specification per structure, one test class per instance.** Laws known to fail are counterexample
  tests, which must find a witness: they document the intended semantics as much as the laws do.
- **A specification takes the instance it checks,** with what its laws need of it in the parameter type, and finds the
  instance's fixture as a given, one per category or promonad, so that the constraint on the category's objects stays
  in the signature. Fixtures of derived categories (`Total.op`, `promonad.arrows`) are givens of their own, because
  implicit search cannot get from `Total.op` back to `Total`.
- **Every test run regenerates `docs/law-status.md`,** the table of laws, instances and statuses; the tests write it
  themselves, independently of the build tool.

## 6. The parser

- **The algebra is a bundle:** `ParserAlgebra(parsers, products, coproducts, zipping, branching, choice, loops, knots)`,
  every combinator an operation of one of them. An interpreter chooses the structures and implements five primitives:
  `lift`, `literal`, `regex`, `rule` and `diagnose`. The semantic types are fixed (`Unit`, `Tuple2`, `Either`,
  `Nothing`, `Vector`): every interpreter made the same choice, and fixing them removes a layer of type members.
- **Ordered choice is override,** derived from the classical structure. `attempt(p): P[A, B + A]`, which runs `p` once
  and reports the outcome, is the form an optimizing interpreter can implement in one pass; `optional` is `attempt`.
  The second alternative is computed only where the first fails, also in the reference, whose classical monad takes
  it by name.
- **Regular expressions are matched in context and by code point,** as `java.util.regex` matches them: `^`, `$`,
  lookbehind and `\b` see the whole input, and a surrogate pair is one character. The optimizing interpreter compiles
  a fragment of them to a scanner that agrees with `java.util.regex` on it, surrogates included.
- **Iteration and recursion are guarded by the input:** a loop step that continues, or a recursive call, must come after
  consumed input, or it fails. Every parser therefore terminates, and repeating an item that consumes nothing fails
  instead of looping or stopping silently.
- **The reference interpreter builds nothing new:** it is the Kleisli category of
  `StateT[Input](OptionT(Writer(Expected.Furthest)))`, and every structure is a generic construction of the library.
  It is the specification, meant to be obviously right; it is slow and not stack-safe.
- **The optimizing interpreter normalizes by laws:** its smart constructors are laws read from left to right, so they
  cannot change what a parser does. Its one analysis that is not a law, the first-set summary `Info`, carries an
  invariant (if a parser succeeds where the next character is `c`, then `c ∈ first`, or it is nullable and consumed
  nothing), which the random law tests check indirectly. It dispatches choices on the next character, records no
  diagnostics on the fast path, and re-runs in a diagnostic mode only when a parse fails.
- **Agreement is the core invariant:** both interpreters give the same results, offsets and diagnostics on every
  grammar without left recursion, checked by random grammars, the law specifications and the JSON grammar.
  `StrictParser` supports left recursion by seed growing, an extension beyond the specification, where the reference
  fails the left-recursive call.

Rejected, until an interpreter needs other semantic types: abstract semantic types and mixin traits for the algebra.

### Diagnostics

- **A parse reports the furthest position at which something failed and the set of expectations there,** each tagged
  with the rules that enclose it. The reports form a join-semilattice, the lexicographic product of the chain of
  positions with sets of expectations, and they are a **writer effect**, produced on success as well as on failure.
  The failure transformer is over the writer, `OptionT(Writer(E))`: `WriterT(E, Option)` would drop the report of a
  parse that fails (`TransformerOrderTest`).
- **The laws force most of this:** the choice monoid needs an associative combination with a unit, and distributivity,
  `h >> (p |> q)` = `(h >> p) |> (h >> q)`, runs `h` twice, which is harmless only if *x* ⊔ *y* ⊔ *x* = *x* ⊔ *y*.
  Commutativity is a choice: it makes the report independent of the order in which alternatives were tried.
- **Tests are silent:** lookahead, negation, `failure` and guard failures report nothing. Keeping the output of a test
  breaks R2 for every writer with a non-trivial output, because a failing test stops the output after it, and breaks
  the zero and complement laws as well (`RestrictionTest` exhibits both). Silent tests keep R2, R3 and the complement
  laws exact and weaken only R1 and R4 to inequations.
- **`rule(p, l)`** reports `l` where `p` fails at or before its start, and otherwise adds `l` to the context of `p`'s
  expectations; tagging preserves joins.
- **The laws come in two tiers:** equations on results, offsets and diagnostics, and inequations *p* ⊑ *q* (same
  results and offsets, *q* reports at least what *p* reports) for right zero, R1 and R4. Every combinator is monotone
  for ⊑, so parsers are enriched over preorders.

Rejected: failures as exceptions (`Try`), whose equality identifies all failures, which no law respects; the reports
are a writer effect instead.

## 7. What the library leaves out

On purpose:
- **total fixed points and iteration on 𝒮,** which cannot exist (§2): unguarded recursion and loops are programs of 𝒫,
  and 𝒮 has the guarded operators;
- **lazy pairs as the product,** until a lazy semantics becomes a target (§2);
- **restriction on 𝒮,** where every arrow is total and restriction is the identity; it lives on 𝒫 (`Partial.Domains`);
- **ordered choice as enrichment over additive monoids,** which it is not: choice distributes on one side only (§4);
- **an `Eq` derived from `CanEqual`** (§5);
- **a hierarchy of enriched categories, functors and promonads** parallel to the ordinary one, until an enriched module
  has a client (§4);
- **examples as library instances** (isomorphisms of particular types, monoids nothing uses), which belong in tests.

Not attempted, each until it has a client: codata and productivity, restriction products as a class, useful fixed
points over products in a strict language, packrat memoization, error recovery, right modules and bimodules, module
morphisms, mixed optics, general iterated enrichment, the delay monad.

## 8. Tooling

- **Tests run in a forked JVM with an explicit heap, and the JSON corpora are parsed on a thread with an explicit
  stack,** so that the outcome does not depend on the machine's defaults; every corpus document is asserted on both
  interpreters.
- **Capture checking everywhere,** in the library and in the tests, so that `->` means a pure function wherever it is
  written. ScalaCheck is not compiled with capture checking, and its generated functions are trusted to be pure.
- **Pants parses with Scalameta,** which the in-repo `scala_override` plugin configures with `Scala3Future`, so that
  dependency inference understands `tracked` parameters.

Rejected:
- safe mode (`-language:experimental.safe`), which would also rule out what capture checking does not track: casts,
  `caps.unsafe`, mutable arrays and captured variables, and references to code not compiled in safe mode (I/O, clocks,
  mutable collections). It holds for a whole compilation or for each file that imports it, and no file can be exempted:
  `StrictParser` needs casts and mutable tables, and the tuple `recursive` of `ParserAlgebra` casts the components of
  its untyped family. Confining it to `category` takes an import in every file or a compilation of its own (an sbt
  project and a Pants resolve). It would check neither totality nor naturality.

## 9. Open issues

- A representing type for equalizers in 𝒮: the limit construction of §4 gives none.
- The compiler issues in [`compiler-issues.md`](compiler-issues.md) remain to be filed.
