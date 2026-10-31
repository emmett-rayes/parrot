# Practical Programming with Categories

*A precise account of category theory for Scala 3 programmers*

Draft of October 26, 2026

---

## Preface

### The missing link

Programmers usually meet category theory through slogans. Types and functions form a category. A `Functor` is a functor. A monad is a monoid in the category of endofunctors. Each slogan points at something real. Almost none of them, as usually stated, says which programs it is about, when two programs count as equal, or which category it means. If those details are filled in carelessly, the slogans become false.

The standard example is Hask, the supposed category of Haskell types and functions, often described informally as "basically Set". In 2016 Andrej Bauer observed that nobody had actually constructed such a category, and that the obvious candidate fails even the identity law because of the way Haskell's `seq` interacts with non-termination [Bauer 2016]. The Haskell wiki's page on Hask now lists the questions that must be settled first: when two morphisms are equal, and which fragment of the language is meant [HaskellWiki]. Even where a category of programs can be built, it is not Set. Chapter 2 shows that it contains only computable functions, so it is far smaller than Set, and chapter 9 shows that it contains polymorphic functions, which sets and functions cannot model in the obvious way.

Scala has the same gap. Libraries provide `Category`, `Functor` and `Monad` type classes, and these are routinely explained as the mathematical notions of the same names. Whether that explanation is true depends on exactly the details the slogans leave out.

### What this document does

This document fills in those details for Scala 3. It assumes a reader who is comfortable with Scala 3 and knows no category theory. By the end, the reader should be able to:

1. understand the basic ideas of category theory, learned from scratch;
2. use those ideas to design programs;
3. define new categories in Scala 3, and test or prove their laws;
4. say precisely what the theory guarantees about that code, and where the guarantee stops.

The emphasis is on the third and fourth points. The literature has many surveys of "category theory in programming"; it has few accounts of what you are actually committing to when you write a category down in a real programming language.

The document comes with a library, `parrot.category`, and a parser-combinator library built on it. Every structure the library defines is explained here, and the library's names are used throughout, so that the library can be read as a consequence of the text.

### The central claim

The whole document develops one claim:

> A category you write in Scala is not an ordinary category of sets and functions. It satisfies two constraints that an ordinary category does not. It is **enriched** in 𝒮, the category of total Scala programs: the arrows between two objects form a Scala type, identity and composition are Scala programs, and the laws hold up to the equality of Scala programs. And it is **uniform**: its objects are Scala types, and its identity and composition are single polymorphic programs that work the same way at every object.

Most of the document traces what follows from these two constraints. Some consequences are restrictions. You cannot form the category of lawful lenses, or the category of relations, the way a mathematician would with sets. Others are gifts: polymorphic code obeys laws you never have to check. Ordinary categories of sets serve throughout as the point of comparison.

Programs that may run forever are not thrown away. They form a second category, 𝒫, which contains 𝒮. Most of Parts I to III is about 𝒮, where reasoning is closest to reasoning about sets; Part IV is about 𝒫 and the other categories of effectful programs that parsers live in.

### The contract and its concessions

Programs form a category only when they behave like mathematical functions. Chapter 2 makes that precise as a **contract** with three clauses: purity, totality, and no observation of how values are represented. Purity and representation independence decide which programs we consider at all. Totality is different: it separates the programs that always terminate, which form 𝒮, from those that may not, which form 𝒫. Scala cannot fully enforce any of the three clauses, so this document makes three practical concessions.

1. **Equality is tested when it can't be proved.** Whether two functions are equal is undecidable in general. Where no proof is available, laws are checked by property-based testing: running each law on thousands of randomly generated inputs.
2. **Purity is checked by capture checking**, Scala's experimental system for tracking side effects in types, together with separation checking or safe mode, which also track mutable variables.
3. **Totality is checked by Stainless where possible, and otherwise asserted by the programmer.** Using a program as an arrow of 𝒮 asserts that it terminates. Like undefined behavior in C, a false assertion voids every conclusion of this document that relied on it. The library makes the assertion explicit: it is the single function `Partial.assumeTotal`, which a search of the code finds wherever the promise is made.

The contract only applies where categorical reasoning is used: to the arrows of your categories, their identities and compositions, and whatever those call. A server's main loop can run forever; it is a program of 𝒫, about which the theory says less. The edges of a program can do I/O; about them the theory says nothing.

These concessions don't weaken the theory. They make explicit where each guarantee comes from: a proof, a tool, a test, or a promise.

### Three languages, kept apart

This document speaks three languages, and much of the confusion in the literature comes from mixing them.

1. **Scala**, the programming language. Its sentences are programs, written in `monospace`.
2. **The language of categories.** Its vocabulary is objects, arrows, identities and composition, and its sentences are equations between composites of arrows, such as g ∘ f = h.
3. **The meta-language**: ordinary mathematics, with sets, functions, "for every" and "there is". We use it to say things *about* Scala programs and *about* categories.

"Hask is Set" is a sentence of the meta-language that silently mixes the other two. It claims that something built from programs equals a mathematical category, without saying how programs become arrows or what equality between arrows means. This document never lets an expression of one language stand in for an expression of another without naming the translation. When a Scala function `f` is used as an arrow, the text says so, and when a set is built from Scala values, it gets its own name, such as Val(A) in chapter 2.

Equality is where mixing does the most damage, so the document uses a different symbol for each kind:

| Symbol | Language | Meaning |
| --- | --- | --- |
| `eq` | Scala | Whether two references point to the same object in memory. Excluded by the contract. |
| `==` | Scala | Scala's universal equality, which calls `equals`. Used only to implement `===` on data. |
| `===` | Scala | The `Eq` type class of section 2.2: a program that decides equality, for types where that is possible. |
| `=?=` | Scala | The `Observable` type class of section 3.3: a program that compares finitely many observations of two values. A test, not a decision, hence the question mark. |
| ≈ | meta | Observational equality of Scala expressions (section 2.4). A relation, not a program. |
| ≐ | meta | Equality of total programs (section 2.6), defined type by type. The equality of arrows in 𝒮. |
| = | meta, category | Equality of mathematical objects. In a category, equality of arrows. |

And for the other basic notation:

| Notation | Language | Meaning |
| --- | --- | --- |
| f : a → b | category | f is an arrow from a to b |
| g ∘ f | category | the composite "g after f" |
| 𝒞(a, b) | category, meta | the collection of arrows from a to b in the category 𝒞 |
| `A -> B`, `A => B` | Scala | function types; `->` marks a pure function (section 2.3) |
| `f: A -> B` | Scala | a value f of that type |
| `f >>> g` | Scala | the composite g ∘ f, written in the order the arrows run (section 3.3) |
| 𝒮, 𝒫 | category | the categories of total programs and of all programs (section 2.8) |
| Val(A) | meta | the set of total values of the Scala type A (section 2.10) |

### Code conventions

All code is written in Scala 3.10.0 with the following compiler options:

```
-source:future -preview -language:experimental.modularity -language:experimental.pureFunctions
-language:experimental.captureChecking -language:strictEquality -Yexplicit-nulls
```

Type classes use the syntax of Scala 3's modularity proposal [Scala type classes, checked]. A type class is a trait or an abstract class with an abstract type member `Self`, not a class with a type parameter. Instances are given with the infix type `is`, as in `given Int is Eq`, and `Int is Eq` stands for the class with `Self` set to `Int`. A context bound such as `[A: Eq]` makes the evidence available under the name of the type parameter, so a method of the instance is written `A.equal`. Where `Self` would be an uninformative name, a type class adds an alias, as in `final type --> = Self`. Data types such as case classes and enums keep ordinary type parameters. The library uses abstract classes for its categorical structures, which take parameters, and traits for type classes without parameters, such as `Eq`, for reasons chapter 11 explains; the code here does the same.

Function types are written `A -> B`. Under capture checking this is the type of *pure* functions; section 2.3 explains why the code insists on it.

**All code is compiled.** A checker, `docs/tutorial/check-snippets.py`, extracts every Scala block of this document and compiles it with the options above. The blocks of a chapter are compiled together and in order, so a later block can use an earlier one, and a chapter that builds on an earlier chapter imports it, as in `import tutorial.ch03.Categories.*`. A block that is meant not to compile is checked to fail, and the text says so. Code in another dialect, such as Stainless, is not compiled, and the text says that too. Parts I and II define everything they use; Parts III and IV use the library.

### How to read this document

Each concept chapter has four parts, matching the four goals above:

- **the idea**, introduced first with sets and functions;
- **why programmers care**;
- **the Scala 3 encoding**;
- **what the theory guarantees**, and where the guarantee stops.

Chapters end with a comparison between Set and Scala and with their own references.

Every non-trivial claim carries a status label.

| Label | Meaning |
| --- | --- |
| **[Proved]** | The argument is given in full in this document. |
| **[Standard]** | A known result, with a reference. References are marked *checked* if the source was consulted while writing this draft, and *from memory* otherwise. |
| **[Assumed]** | Believed and used, but not proved here. Listed in the ledger (appendix B). |
| **[Convention]** | A promise the programmer makes. No tool enforces it. |
| **[Checked: tool]** | Enforced by the named tool. |
| **[Tested]** | Supported by property-based tests only. The library's law status table (chapter 22) records each such law. |
| **[Tested: counterexample]** | A law that does not hold, with a counterexample that the tests find and the law status table records. |
| **[Open]** | Not known. |
| **[Exploration]** | We are trying something out to see what happens. Nothing in such a passage is established. |

### Plan

| Part | Chapters |
| --- | --- |
| I. What a Scala category is | 1. Categories, starting from sets · 2. Programs: 𝒫 and 𝒮 · 3. Defining your own category · 4. What you actually defined: enriched categories |
| II. Consequences | 5. Arrows are programs · 6. No subset types · 7. No quotient types · 8. Objects must be types · 9. Uniformity's payoff: parametricity · 10. One kind per class |
| III. Working with categories | 11. Encoding categories in Scala 3 · 12. Functors, bifunctors and profunctors · 13. Natural transformations, Yoneda and equivalence · 14. Universal constructions and monoidal structure · 15. Monads, monoid objects and adjunctions · 16. Recursion on categories |
| IV. Effects as structure | 17. Promonads and Freyd categories · 18. Partiality: restriction categories · 19. Iteration and recursion on promonads · 20. Case study: parser combinators |
| V. Map and tools | 21. The boundary map · 22. Tools and workflow |
| Appendices | A. The formal core · B. Ledger · C. Glossary · D. What the library leaves out · E. Concept index |

---

# Part I. What a Scala category is

## Chapter 1. Categories, starting from sets

### 1.1 The idea

Start with something every programmer already knows: functions between sets. Take A = {1, 2, 3} and B = {red, green}, and let f : A → B send 1 and 2 to red and 3 to green. Given another function g : B → C, you can form the **composite** g ∘ f : A → C, defined by (g ∘ f)(x) = g(f(x)). Read g ∘ f as "g after f". Every set A also has an **identity** function id_A : A → A with id_A(x) = x.

Three facts about these operations are so familiar that they are easy to overlook.

- **Associativity.** For f : A → B, g : B → C and h : C → D, h ∘ (g ∘ f) = (h ∘ g) ∘ f. Both sides send x to h(g(f(x))).
- **Left identity.** id_B ∘ f = f.
- **Right identity.** f ∘ id_A = f.

Category theory takes these three facts as the definition of its subject and forgets everything else. It forgets what is inside a set, and it even forgets that arrows are functions.

**Definition 1.1 (category).** A category 𝒞 consists of:

1. a collection of **objects**;
2. for every two objects a and b, a collection 𝒞(a, b) of **arrows** from a to b; we write f : a → b for an arrow in 𝒞(a, b);
3. for every object a, an **identity arrow** id_a : a → a;
4. for every two arrows f : a → b and g : b → c, a **composite** arrow g ∘ f : a → c;

such that composition is associative and the identity arrows are left and right identities, exactly as in the three laws above.

Some vocabulary. Arrows are also called **morphisms**. The collection 𝒞(a, b) is called a **hom-set**, short for "set of homomorphisms". For f : a → b, the object a is the **source** of f and b is its **target**. Composition g ∘ f is only defined when the target of f is the source of g, just as a function can only be applied to an argument of the right type.

Category theorists often draw arrows as diagrams. A diagram **commutes** when every two paths between the same two objects compose to the same arrow. The diagram

```
      f        g
  a ─────▶ b ─────▶ c
  │                 ▲
  └───────h─────────┘
```

commutes exactly when h = g ∘ f. Diagrams are only a notation for equations between composites, and this document mostly writes the equations.

### 1.2 Examples

**Sets.** The category **Set** has sets as objects and functions as arrows, with ordinary composition and identities. It is the example the definition was abstracted from.

**A preorder.** The integers with ≤ form a category. The objects are the integers. There is exactly one arrow a → b when a ≤ b, and no arrow otherwise. The identity arrow a → a exists because a ≤ a. Composition exists because a ≤ b and b ≤ c imply a ≤ c. The laws hold automatically: there is at most one arrow between any two objects, so any two arrows with the same source and target are equal. Any relation that is reflexive and transitive, called a **preorder**, gives a category in the same way. Here the arrows are not functions at all; they are facts. Preorders return twice: in chapter 14, where least upper bounds in a preorder, called joins, turn out to be a categorical construction, and in chapter 20, where a preorder on parsers compares the error messages they produce.

**A monoid.** A **monoid** is a set M with an associative operation · and an element e such that e · m = m = m · e for every m. Strings under concatenation, with the empty string as e, form a monoid. So do the integers under addition with 0, and under multiplication with 1. Every monoid is a category with a single object ⋆: the arrows ⋆ → ⋆ are the elements of M, composition is ·, and the identity arrow is e. The category laws are exactly the monoid laws, so a monoid *is* a one-object category. Here the arrows are data.

**Relations.** The category **Rel** has sets as objects, and an arrow A → B is a relation R ⊆ A × B, that is, a set of pairs. Composition is

S ∘ R = { (a, c) | there is some b with (a, b) ∈ R and (b, c) ∈ S },

and the identity on A is the equality relation { (a, a) | a ∈ A }. Notice the "there is some b" in the definition of composition. It becomes important in chapter 5.

**Matrices.** The category **Mat** has the natural numbers as objects. An arrow n → m is an m × n matrix of integers, composition is matrix multiplication, and the identity on n is the n × n identity matrix. Composing an m × n matrix with a k × m matrix gives a k × n matrix, so the sources and targets line up as they should. Here the objects are numbers, the arrows are grids of numbers, and no set of elements is in sight.

The lesson of these examples is that objects need not be sets and arrows need not be functions. All a category records is how its arrows compose.

### 1.3 Isomorphisms, and the leverage of laws

An arrow f : a → b is an **isomorphism** if there is an arrow g : b → a with g ∘ f = id_a and f ∘ g = id_b. We then write a ≅ b, say that a and b are **isomorphic**, and call g an **inverse** of f. In Set the isomorphisms are the bijections. In Mat they are the invertible square matrices. In the preorder of integers the only isomorphisms are the identities, because a ≤ b and b ≤ a force a = b. In the monoid of strings only the empty string has an inverse.

Isomorphic objects are indistinguishable by anything the category can express: every arrow into or out of one of them can be transported along the isomorphism to the other. Category theory therefore rarely asks whether two objects are *equal*, and almost always asks whether they are isomorphic.

**Proposition 1.2.** An arrow has at most one inverse. **[Proved]**

*Proof.* Suppose g and g′ are both inverses of f : a → b. Then

g = g ∘ id_b = g ∘ (f ∘ g′) = (g ∘ f) ∘ g′ = id_a ∘ g′ = g′.

The steps use, in order, right identity, the fact that g′ is an inverse, associativity, the fact that g is an inverse, and left identity. ∎

The proof uses nothing but the category laws. So it holds in Set, in Mat, in every monoid, and in every category you will define in Scala later in this document. This is the main reason to care about categories: an argument made once, from the laws alone, applies to every structure that satisfies them.

### 1.4 Maps between categories: functors

Categories are compared by maps that preserve their structure.

**Definition 1.3 (functor).** A **functor** F from a category 𝒞 to a category 𝒟, written F : 𝒞 → 𝒟, assigns to every object a of 𝒞 an object F(a) of 𝒟, and to every arrow f : a → b of 𝒞 an arrow F(f) : F(a) → F(b) of 𝒟, such that

- F(id_a) = id_F(a) for every object a, and
- F(g ∘ f) = F(g) ∘ F(f) for every composable f and g.

A functor sends identities to identities and composites to composites. Four examples:

- **String length** is a functor from the one-object category of strings under concatenation to the one-object category of natural numbers under addition. Its object map is forced, since there is only one object on each side, and its arrow map sends a string to its length. The functor laws say length("") = 0 and length(s ++ t) = length(s) + length(t). A functor between one-object categories is exactly a **monoid homomorphism**.
- **Doubling** n ↦ 2n is a functor from the preorder of integers to itself. The arrow map has nothing to choose: if a ≤ b then 2a ≤ 2b, so the unique arrow a → b goes to the unique arrow 2a → 2b. A functor between preorders is exactly a **monotone map**.
- **The determinant** is a functor from the one-object category of n × n integer matrices under multiplication to the integers under multiplication: det(I) = 1 and det(AB) = det(A) det(B).
- **The graph** of a function is a functor from Set to Rel. It is the identity on objects and sends a function f : A → B to the relation { (a, f(a)) | a ∈ A }. The graph of an identity function is the equality relation, and the graph of a composite is the composite of the graphs.

Every category has an identity functor, and functors compose, by composing their object maps and their arrow maps.

Two properties of functors matter throughout this document. Fix a functor F : 𝒞 → 𝒟 and two objects a and b. F sends arrows a → b to arrows F(a) → F(b), so it defines a function between hom-sets, 𝒞(a, b) → 𝒟(F(a), F(b)).

- F is **faithful** if each of these functions is injective: different arrows go to different arrows.
- F is **full** if each of these functions is surjective: every arrow F(a) → F(b) is the image of some arrow a → b.

The graph functor Set → Rel is faithful, because different functions have different graphs, but not full, because most relations are not graphs of functions. String length is not faithful, since "ab" and "ba" have the same length, but it is full, since every natural number is the length of some string.

Why care? The two properties tell you which reasoning can move across a functor.

- If F is faithful, then to prove that two arrows f and g of 𝒞 are equal, it suffices to prove F(f) = F(g) in 𝒟. **Equations can be checked in the target.**
- If F is full, then whenever you construct an arrow F(a) → F(b) in 𝒟, there is an arrow a → b in 𝒞 that F sends to it. **Existence can be pulled back from the target.**

A faithful functor that is not full is the typical relationship between something concrete and a richer world it sits inside. Equations transfer back; constructions do not. Chapter 2 shows that this is exactly the relationship between Scala programs and Set.

### 1.5 Hom-sets are sets

In every example above, the arrows between two objects form a set. Look again at Definition 1.1 with that in mind. The identity on a is an element of the set 𝒞(a, a). Composition is a function

𝒞(b, c) × 𝒞(a, b) → 𝒞(a, c)

that takes a pair of arrows to their composite. The laws are equations between such functions. So the definition of a category quietly uses sets, pairs and functions to describe its own structure.

Are categories of this kind just the **locally small** categories? Yes. A category is locally small when every hom-collection 𝒞(a, b) is a set rather than something larger, and that is precisely what it takes for the hom-collections to be objects of Set. So the locally small categories are exactly the categories **enriched in Set**, or **Set-enriched** categories **[Standard: Kelly 1982, from memory]**. The collection of *objects* may still be too big to be a set: the collection of all sets is not itself a set, yet Set is locally small.

The two names emphasize different things. "Locally small" is about size. "Set-enriched" is about what kind of thing a hom is and what kind of thing composition is: a set, and a function. The second reading is the one this document cares about, because it generalizes. Chapter 4 replaces Set by 𝒮, the category of total Scala programs, and that replacement is the central idea of the document.

All categories in this document are locally small, and the size of the object collection never matters here.

### 1.6 Why programmers care

Composition is how programs are built. Data pipelines, middleware stacks, parser combinators, database migrations and user-interface state transitions are all things that are chained together. A category is the smallest interface for "things that chain". It asks for a way to do nothing, the identity, and a way to chain, composition. And it requires that chains can be regrouped freely (associativity) and that doing nothing is harmless (the identity laws).

Those laws are what make everyday refactoring safe. Associativity lets you extract part of a pipeline into a helper, or inline it again, without changing the result. The identity laws let you delete a stage that does nothing. Because an argument from the laws, like Proposition 1.2, holds for every lawful instance, generic code written against the category interface is correct for every lawful instance. Chapter 3 gives an algorithm of this kind.

Functors are translations between worlds of composition. String length turns concatenation into addition, which is why the total length of a large text can be computed by splitting it into pieces, measuring them in parallel, and adding up the results. Every map-reduce computation rests on a monoid homomorphism of this kind.

### 1.7 Exploration: do Scala functions form a category?

**[Exploration]** Let us try the obvious thing and see what happens. Scala functions compose with `andThen` and `compose`:

```scala
val trim:   String -> String = _.trim
val length: String -> Int    = _.length
val double: Int -> Int       = _ * 2

val pipeline: String -> Int = trim andThen length andThen double
```

The arrow `->` in these types marks a function without side effects. Section 2.3 explains it; for this experiment it behaves like the familiar `=>`.

`f andThen g` applies f first, and `g compose f` is the same function written in mathematical order. There is an `identity` function. So it looks as if Scala types and functions might form a category, with types as objects and functions as arrows. Try checking a law:

```scala fails
val f: Int -> Int = _ + 1
val sameAsF = (f andThen identity) == f
```

The right identity law says that f composed with the identity is f. In ordinary Scala this comparison compiles and answers `false`. The reason is that `==` on function values compares references: it asks whether two function objects are the same object in memory, not whether they compute the same thing. The code in this document is compiled with strict equality (section 2.2), under which the comparison does not compile at all: the compiler refuses to compare functions with `==`.

What has this experiment shown? Not that Scala functions fail to form a category, and not that they succeed. It has shown that *if* there is a category whose arrows are Scala functions, its notion of equality cannot be `==`. Equality was never specified, and the experiment made the gap visible. Here the failure was immediate. With subtler candidates for equality, a careless choice can look right for a long time, which is why chapter 2 constructs the category carefully instead of continuing to experiment.

### 1.8 Set and Scala

In Set, the category laws are theorems of set theory, true without conditions, because equality of functions is simply equality of their outputs on every input and sets contain nothing but their elements. For Scala functions, whether the laws hold depends on two choices this chapter has not yet made: which programs count as arrows, and what it means for two of them to be equal. A careless answer to either question gives something that is not a category at all. That is the gap the slogans skip, and closing it is the job of chapter 2.

| | Set | Scala functions, so far |
| --- | --- | --- |
| Objects | sets | types, perhaps |
| Arrows | functions | function values, perhaps |
| Equality of arrows | same output on every input | not yet defined; `==` fails |
| Laws | theorems | not yet meaningful |

### References for chapter 1

- Saunders Mac Lane, *Categories for the Working Mathematician*, 2nd ed., Springer, 1998. (From memory.)
- Steve Awodey, *Category Theory*, 2nd ed., Oxford University Press, 2010. (From memory.)
- G. M. Kelly, *Basic Concepts of Enriched Category Theory*, Cambridge University Press, 1982. (From memory.)

---

## Chapter 2. Programs: 𝒫 and 𝒮

### 2.1 What would the objects and arrows be?

The exploration in section 1.7 suggested a category with types as objects and functions as arrows. Before any law can be checked, that suggestion has to be made precise, because "type" and "function" each play more than one role in Scala.

**Objects.** The objects are the **closed** Scala types of **kind \***: types that have values and mention no type variables, such as `Int`, `String`, `List[Int]`, `(Int, String)` and `Int -> Boolean`. A type constructor such as `List` is not an object, because it has no values until it is given an argument; categories whose objects are type constructors appear in chapters 10 and 12. Nor is `A -> A` inside a definition `def f[A]`, because `A` is a variable there; `A -> A` names a whole family of objects, one for each choice of `A`, and families of this kind are the subject of chapters 9 and 13.

**Arrows.** An arrow from A to B is a function value of type `A -> B`. The identity on A is `(a: A) => a`, and the composite of f : A → B and g : B → C is `(a: A) => g(f(a))`.

**Three roles of a function.** Function types make this subtle, because a function type is itself a type. Fix a function value `f: Int -> Boolean`.

- The type `Int -> Boolean` is an **object**, like any other closed type.
- The value `f`, regarded as a way of getting from `Int` to `Boolean`, is an **arrow** Int → Boolean.
- The same value `f`, regarded as a piece of data that can be stored in a list or passed to another function, is a **value of the object** `Int -> Boolean`.

The same three roles coexist in Set. The set of all functions from A to B is a set, so it is an object; a particular function is an arrow; and that function is also an element of the set of all functions. Chapter 14 makes the correspondence precise: arrows A → B correspond exactly to values of `A -> B`, and this is what it means for a category to have function types. Until then, the word "arrow" means a function value in its role as a morphism, and "value of type `A -> B`" means the same thing in its role as data. Note which language each sentence belongs to. "`f` has type `Int -> Boolean`" is a sentence about Scala. "f is an arrow Int → Boolean" is a sentence of the meta-language, saying how a Scala value is to be read in the category language.

What could go wrong? Section 1.7 showed one problem: equality. There are others, because many Scala "functions" do not behave like mathematical functions at all. This chapter first builds an equality that works for data (section 2.2) and restricts the programs that count (section 2.3). It then defines equality for all types (section 2.4), shows why programs that may run forever have to be kept apart from those that cannot (section 2.5), and defines the programs that always terminate, with their equality, type by type (section 2.6). After a look at evaluation order and recursion (section 2.7), it defines not one category but two: 𝒫, of all programs, and 𝒮, of the total ones (section 2.8).

### 2.2 Equality on data: `===`

Equality has to be built from the ground up, starting with types whose values a program can actually compare.

**Data types.** Call a type a **data type** if it is built from `Boolean`, `Char`, `Int`, `Long`, `BigInt`, `String` and `Unit` using tuples, `Option`, `Either`, `List`, and case classes or enums whose equality is the one the compiler generates, provided no component is a function or a value of an abstract type. A value of a data type is a finite tree of constructors with primitive values at the leaves. Two such values are equal exactly when they are the same tree.

For data types we can write equality as a program. Here is the type class this document uses, with its laws stated inside it; it is the library's `Eq`, apart from one detail that section 3.8 adds:

```scala
trait Eq extends caps.Pure:
  type Self
  def equal(a: Self, b: Self): Boolean
  extension (a: Self) def ===(b: Self): Boolean = equal(a, b)

  // Laws. Each must return true for all arguments.
  object EqLaws:
    def reflexivity(a: Self): Boolean                     = a === a
    def symmetry(a: Self, b: Self): Boolean               = !(a === b) || (b === a)
    def transitivity(a: Self, b: Self, c: Self): Boolean = !(a === b && b === c) || (a === c)

object Eq:
  /** Structural equality, for data types whose `==` compares constructor trees. */
  def structural[A](using CanEqual[A, A]): A is Eq = new Eq:
    type Self = A
    def equal(a: A, b: A): Boolean = a == b

  given IntIsEq: (Int is Eq)         = structural
  given LongIsEq: (Long is Eq)       = structural
  given BooleanIsEq: (Boolean is Eq) = structural
  given StringIsEq: (String is Eq)   = structural
  given BigIntIsEq: (BigInt is Eq) =
    given CanEqual[BigInt, BigInt] = CanEqual.derived
    structural

  given OptionIsEq: [A: Eq] => Option[A] is Eq:
    def equal(a: Option[A], b: Option[A]): Boolean = (a, b) match
      case (Some(x), Some(y)) => x === y
      case (None, None)       => true
      case _                  => false

  given Tuple2IsEq: [A: Eq, B: Eq] => (A, B) is Eq:
    def equal(a: (A, B), b: (A, B)): Boolean = a._1 === b._1 && a._2 === b._2

import Eq.given
```

The final import brings the instances into scope, so that `===` can be used on `Int`, `Option[Int]` and so on in the code that follows. The laws live in an object nested in the class, `EqLaws`, as they will in every type class of this document and of the library. `extends caps.Pure` declares that an instance of `Eq` is a pure value. Capture checking, which section 2.3 introduces, needs the declaration because the laws refer to the instance; every type class in this document makes it.

`===` is the only equality the code in this document uses on values. Scala's `==` appears in exactly one place, inside `Eq.structural`, and that place is one *special case* of `Eq`: the case of types whose compiler-generated `equals` compares structure. There are other special cases. `Double` is not a data type, because its `==` is not even reflexive: `Double.NaN == Double.NaN` is `false`. It still gets a lawful instance, built on `java.lang.Double.compare`, which treats every NaN as equal to itself and distinguishes `0.0` from `-0.0`:

```scala
given DoubleIsEq: Double is Eq:
  def equal(a: Double, b: Double): Boolean = java.lang.Double.compare(a, b) == 0
```

To keep `==` from creeping in elsewhere, this document compiles with strict equality. Under strict equality, `==` compiles only for types with a `CanEqual` instance, and the fallback that otherwise allows `==` between any two values is switched off [Multiversal equality, checked]. Function types have no `CanEqual` instance, so comparing two functions with `==` becomes a compile error, as section 1.7 found. Add `derives CanEqual` to your data types, but never to a type with function-valued fields: `==` on it would compare those functions by reference.

**Functions have no `Eq`.** No lawful `Eq` instance exists for `BigInt -> Boolean`, or for any function type with an infinite argument type and a non-trivial result type.

**Proposition 2.1.** No program decides whether two functions of type `BigInt -> Boolean` return the same result on every argument. **[Standard: reduction to the halting problem]**

*Proof.* For any program e, let `p_e` be the function that, given n, runs e for n steps and returns `true` if e has not halted yet. Each `p_e` is a terminating, computable function. It returns `true` on every argument exactly when e never halts. A program deciding whether `p_e` equals `_ => true` would therefore decide the halting problem, which is impossible. ∎

So data have a decidable equality and functions do not. The rest of this chapter defines equality for functions anyway, as a relation of the meta-language rather than as a program, and chapter 3 shows how it can still be tested.

### 2.3 The contract

Even with equality on data settled, three kinds of Scala program get in the way of a category. The **contract** describes them in three clauses. Two of them, purity and representation independence, restrict the *language*: they decide which programs we consider at all. The third, totality, is different. It is a property that some programs of that language have and others lack, and section 2.8 uses it to sort programs into two categories. For each clause, this section says what it requires, why, and what checks it.

#### C1. Purity

**Statement.** A function's result depends only on its argument, and calling it has no effect other than producing that result. It does not mutate shared state, perform input or output, read a clock, or draw random numbers.

**Why.** Consider

```scala
def counting(): Boolean =
  var counter = 0
  val next: Unit => Int = _ => { counter += 1; counter }
  next(()) === next(())
```

`counting()` is `false`: `next` gives different results for the same argument. So `next` does not determine a function from `Unit` to `Int` at all. The natural equality on functions, "same result on every argument", is then not even reflexive, since `next` disagrees with itself. Without an equivalence relation on arrows there is no category. The other exclusions are instances of the same two failures. A function that reads a clock or a random generator gives different results for the same argument. A function that writes to shared state or performs output has an effect that another part of the program can observe, so replacing one call by its result changes behavior.

Effects are not wrong. They have to be made visible in types before they can be modeled, and chapter 15 shows how monads do this, while Part IV builds categories out of effectful programs directly.

**Checked by capture checking.** Under capture checking, the arrow `A -> B` is the type of pure functions, which cannot retain any capability, while `A => B` may retain arbitrary capabilities [Capture checking overview, checked]. That is why the code in this document writes `->`: every function it calls an arrow of a category has a type that says the function is pure. There is one gap to know about. In Scala 3.10.0, capture checking on its own tracks capabilities that are passed around as values, but not local mutable variables: `counting` above still type-checks when `next` is declared `Unit -> Int`. Separation checking, a further experimental layer, does track them, and then the pure declaration is rejected **[Checked: Scala 3.10.0]**:

```scala unit=Separation fails
import language.experimental.separationChecking

def counting(): Int =
  var counter = 0
  val next: Unit -> Int = _ => { counter += 1; counter }
  next(())
```

**Safe mode**, `import language.experimental.safe`, also tracks all mutation, and goes further. It forbids unchecked casts and pattern matches, the `caps.unsafe` module, `@unchecked` annotations and runtime reflection, and it allows access to a global object only if that object is itself implemented safely [Safe mode, checked]. All three features are experimental. The reference describes capture checking as fairly mature and expected to stabilize soon, and separation checking as still in flux.

**What separation checking would add.** Capture checking records *which* capabilities a function may use. Separation checking records *who else* may use them. Classes extending `Mutable` mark their mutating methods with `update`; references are either read-only or exclusive; and `consume` parameters transfer exclusive ownership of a capability to the callee [Capture checking overview, checked; VirtusLab, checked]. For this document, the interesting consequence would be functions that mutate state they exclusively own. A function that consumes a buffer, appends to it in place and returns it cannot be distinguished from a pure function on immutable buffers, because nobody else can observe the old version. If that is right, separation checking would let efficient in-place implementations count as arrows of 𝒮. The idea is the one behind uniqueness types in the language Clean **[Standard, from memory]**, but for Scala's separation checking it has not been established **[Open]**. There is also a catch for the theory: an exclusively owned value cannot be duplicated freely, and section 4.2 explains why that takes us outside the kind of enrichment this document studies.

**Gaps.** Safe mode does not rule out exceptions; the reference says so explicitly and relies on runtime containment instead [Safe mode, checked]. Exceptions are therefore covered by C2. A library can be marked `@assumeSafe`, which moves the obligation to verify it onto the programmer.

#### C2. Totality

**Statement.** Applied to any argument, a function terminates and returns a value. It does not loop forever, throw an exception, or overflow the stack.

Exceptions are included because a function that throws returns no value. For the theory this is the same as not terminating, and Scala gives both the same type: `throw e` and an infinite loop both have type `Nothing`. The contract also idealizes resources: a function that would terminate given enough stack and memory counts as total.

"Any argument" needs care when the argument is itself a function, which may or may not terminate. Section 2.6 makes the statement precise, type by type.

**Why.** Section 2.5 proves that if non-termination is allowed, something basic about types has to give: either `Nothing` stops behaving like an empty type, or function application stops behaving like substitution.

**Programs that break C2 are not thrown away.** C1 and C3 decide which programs we consider; C2 does not. A program that may loop or throw is still a program, and section 2.8 makes it an arrow of a category 𝒫 of all programs. What C2 decides is membership in the smaller category 𝒮 of total programs, where reasoning is as strong as in Set. Using a program as an arrow of 𝒮 is therefore a *claim* that it terminates.

**Checked by Stainless, or asserted.** Stainless verifies termination for code in its supported subset of Scala, along with the absence of certain runtime errors such as non-exhaustive matches [Stainless README, checked]. It currently supports only the Scala 3 front end, from version 3.5.0 on, and verified code is typically written against Stainless's own library, such as `stainless.collection.List`, rather than the standard library. Outside that subset, totality is **[Convention]**: the programmer asserts it. An assertion that turns out false voids every conclusion that relied on it, as undefined behavior does in C. Section 2.8 shows how the library makes the assertion visible in the code.

Stainless also supports *laws*. Its authors have demonstrated hierarchies of algebraic structures in which laws are declared once, in the abstract structure, and proved by Stainless whenever the structure is instantiated [Kunčak 2020, checked]; the laws are marked with an annotation, `@law` (from memory). This is exactly the shape of the law design in chapter 3, where laws live inside the type class as Boolean-valued methods. The limitation is the dialect. Stainless's documented subset is built around abstract classes and case classes with invariant type parameters [Stainless PureScala docs, checked], and we have found no indication that it accepts the modularity syntax this document uses, with `Self` type members and `is` **[Open]**. So in this document, Stainless proofs are written as separate lemmas in Stainless's dialect that state the same Boolean laws.

When a function is genuinely partial and should still be an arrow of 𝒮, make the partiality visible in its type by returning `Option[B]` or `Either[E, B]`. Addendum 2.A compares this with Scala's `PartialFunction`.

#### C3. No observation of representations

**Statement.** A program may observe a value only through the operations its type provides, never through how the value happens to be represented in memory.

This is the principle of **representation independence**: if the operations of a type cannot tell two values apart, the values must be interchangeable. It has two consequences that this document relies on everywhere. It is what makes equality of functions extensional (section 2.6), and it is what makes polymorphic functions obey free theorems (chapter 9). Concretely, C3 excludes the following, and each exclusion breaks something different.

1. **`eq` and `ne`.** These reveal whether two references point to the same object in memory. `(f andThen identity) eq f` is `false`, although the two functions agree on every argument, so with `eq` a program can tell f ∘ id apart from f and the right identity law fails for every f. Two equal strings built separately can be told apart in the same way. With `eq`, equality would depend on how and when values were allocated.
2. **`null`.** `null` is an extra value of every reference type. It breaks case analysis: a value of type `Option[A]` might be `null`, so the two-case proofs of chapter 3, which consider only `None` and `Some`, become false, and `(null: Option[Int]).flatMap(f)` throws. A `null` function throws when applied, breaking C2. Scala's explicit-nulls mode removes `null` from ordinary reference types and checks this exclusion **[Standard, from memory]**.
3. **Type tests: `isInstanceOf`, and pattern matching on values of abstract type, of an unbounded type parameter, or of type `Any`.** These let a polymorphic function inspect its type argument at run time and behave differently at different types:

    ```scala
    def notId[A](x: A): A = x match
      case i: Int => (i + 1).asInstanceOf[A]
      case _      => x
    ```

    The compiler accepts this, with a warning. Chapter 9 shows that every function of type `[A] => A => A` that respects C3 is the identity. `notId` is not, so type tests destroy that guarantee and every other free theorem. They also break abstraction: the reference shows how a match can expose an immutable array type as a mutable `Array` and modify it [Matchable, checked].
4. **Casts: `asInstanceOf`.** A cast can throw `ClassCastException`, breaking C2. It can forge a value of an abstract type that the type's own operations would never produce, breaking the invariants that abstraction is meant to protect. And like type tests, it lets polymorphic code depend on its type argument.
5. **Runtime reflection.** Reflection can read private fields, class names and method lists. Two implementations of the same interface that differ only in their private representation are observationally equal by the interface, but reflection tells them apart.
6. **`hashCode`, `toString` and `getClass` on functions and on values of abstract type.** On a function, these reveal the compiled class and an identity-based hash, so they distinguish f from f ∘ id just as `eq` does. On a value of an abstract or opaque type, they reveal the representation: an opaque `Meter` implemented as a `Double` prints as a `Double`. On data types, the compiler-generated `toString` and `hashCode` are determined by the structure and are harmless.
7. **Custom `equals` on data types.** `Eq.structural` relies on `equals` comparing structure. A custom `equals` that ignores a field makes `===` report equality between values that a program can tell apart by reading that field, so `===` would claim more than is true. A custom `equals` that is not reflexive or transitive breaks the laws of `Eq` itself.

**Partly checked.** Strict equality makes `==` on functions a compile error (section 2.2). The `Matchable` trait makes the compiler warn about pattern matches on `Any`, on unbounded type parameters and on abstract types, under `-source future-migration` or later [Matchable, checked]; since this document compiles with `-source:future`, those warnings are on, and `notId` above triggers one. Safe mode forbids unchecked casts and pattern matches and runtime reflection [Safe mode, checked]. Explicit nulls covers `null`. Nothing checks `eq`, `hashCode`, `toString` or custom `equals`, so for those C3 is **[Convention]**.

#### Summary of the contract

| Clause | Decides | Checked by | Not checked |
| --- | --- | --- | --- |
| C1 Purity | which programs we consider: no mutation of shared state, I/O, clocks, randomness | capture checking with `->`; separation checking or safe mode for mutable variables | code marked `@assumeSafe` |
| C3 Representation independence | which programs we consider: no `eq`, `null`, type tests, casts, reflection, `hashCode`/`toString`/`getClass` on functions and abstract types, custom `equals` | strict equality, `Matchable` warnings, safe mode, explicit nulls | `eq`, `hashCode`, `toString`, custom `equals` |
| C2 Totality | which programs are arrows of 𝒮: termination, no exceptions, no stack overflow | Stainless, on its supported subset | everything else: an assertion |

Whether a given program keeps the contract is undecidable in general, which is why the contract relies on tools and assertions.

### 2.4 Observational equality

With the language fixed by C1 and C3, equality can be defined for every type.

**Definition 2.2 (observational equality).** A **context** for type A is a program of the language, of a data type, with a hole where an expression of type A fits. Two expressions s and t of type A are **observationally equal**, written s ≈ t, if for every context C, either C[s] and C[t] both fail to terminate, or both terminate with results equal by `===`.

Two details of this definition matter. First, the contexts are *all* programs of the language, terminating or not. The definition does not mention C2, so it does not depend on the totality that section 2.6 will define in terms of it. Second, termination is itself an observation: a context can tell an expression that terminates from one that does not, simply by running it.

Observational equality is the right notion because it is exactly the guarantee a programmer wants. If s ≈ t, then replacing s by t anywhere in a program cannot change anything the program can observe. That is what "refactoring is safe" means.

**Proposition 2.3.** Observational equality is an equivalence relation, and it is a **congruence**: if s ≈ t, then putting s and t into the same surrounding expression gives observationally equal results. **[Proved]**

*Proof.* Reflexivity, symmetry and transitivity follow from the same properties of `===` on data types, applied to each context C. For the congruence property, suppose s ≈ t and let E be a surrounding expression with a hole. Any context C for the type of E gives a context for the type of s: put E into C's hole and s or t into E's hole. Since s ≈ t, that combined context cannot tell s from t, so E[s] ≈ E[t]. ∎

On data types, observational equality and `===` should agree, and half of that is immediate. If s ≈ t and s terminates, take C to be the context consisting of just the hole: then t terminates too and s === t. **[Proved]** The converse, that structurally equal data cannot be told apart by any context, relies on C3, because only representation-level operations such as `eq` could distinguish two equal trees. It is part of assumption A1 in section 2.6.

### 2.5 Why totality is not optional

Definition 2.2 allows programs that never terminate. This section explains why that is a problem for a category that is meant to behave like Set, and therefore why section 2.6 sets the total programs apart. The argument is short, but it rests on three properties of a programming language, each of which looks desirable on its own. They are worth understanding one at a time first.

#### Three desirable properties

**(E) Emptiness: any two functions of type `Nothing -> B` are equal.**

Scala's `Nothing` has two faces. In the type checker it is the *bottom type*, a subtype of every other type. In the intended semantics it is the *empty type*, the type with no values. Property (E) is the precise form of the second face.

Why this formulation? In Set, the empty set ∅ is characterized among all sets by a property of its functions: for every set B there is exactly one function ∅ → B, the empty function, which has nothing to do. Category theory calls an object with this property an **initial object**, and chapter 14 shows that being initial pins an object down up to isomorphism. So "Nothing is empty" is not best stated as "Nothing has no values", which is a statement in the meta-language about Scala's semantics. In the language of categories it is stated as: there is exactly one arrow from `Nothing` to every type. There is always at least one, because `Nothing` is a subtype of everything:

```scala
def absurd[B]: Nothing -> B = n => n
```

So (E) says there is at most one, which is the content of "Nothing behaves like ∅".

(E) is what makes case analysis work with unreachable cases. It is why `Either[A, Nothing]` behaves like `A`, why `Option[Nothing]` behaves like `Unit`, and why a branch that receives a `Nothing` can return anything at all without affecting the program's meaning.

**(B) Substitution: applying a function literal `(x: A) => body` to an expression `e: A` is equal to `body` with e substituted for x.**

This is the computation rule for functions, known as **β-reduction**. It is what equational reasoning about programs means at its most basic. Every time you inline a helper function, or replace a call by the function's body with the argument plugged in, you are using (B). In Set, (B) is not even a rule; it is what function application is.

**(D) Divergence: there is an expression `z: Nothing`.**

Scala has many:

```scala
def loop(): Nothing = loop()        // general recursion
def fail(): Nothing = throw Error() // exceptions
def todo(): Nothing = ???           // the placeholder, which throws
```

Any language with general recursion has (D), because a function can be defined to call itself forever, and any language with exceptions has it too. (D) is the price of Turing completeness and of convenient error handling.

#### The theorem

**Theorem 2.4 (something has to give).** **[Proved]** Suppose a language and an equality ≈ on its expressions satisfy (E), (B) and (D), and that applying equal functions to the same argument gives equal results. Then any two expressions of the same type are equal.

*Proof.* Let b₁ and b₂ be any two expressions of a type B. Define the functions `k1 = (_: Nothing) => b1` and `k2 = (_: Nothing) => b2`. By (E), k1 ≈ k2, so k1(z) ≈ k2(z), where z is the expression provided by (D). By (B), k1(z) ≈ b₁ and k2(z) ≈ b₂. Hence b₁ ≈ b₂. ∎

The extra assumption, that equal functions applied to the same argument give equal results, holds for any sensible equality, because it is part of being a congruence (Proposition 2.3). So the theorem says: **a language in which any two values differ must give up one of (E), (B) and (D).** All three choices describe real languages.

| World | Gives up | Why | What happens |
| --- | --- | --- | --- |
| Scala, all programs (the category 𝒫 of section 2.8) | (B) | Scala evaluates the argument before calling a function. | `k1(loop())` never returns b₁. Substitution holds only when the argument is a value that has already been computed. |
| Haskell (lazy) | (E) | Haskell evaluates an argument only when it is needed. | `\_ -> 1` and `\_ -> 2` of type `Void -> Int` differ when applied to `undefined`: one gives 1, the other 2. `Void` is not initial. |
| Scala, total programs (the category 𝒮 of section 2.8) | (D) | C2 requires termination. | No expression of type `Nothing` can be evaluated. (E) and (B) both hold. |

Giving up (B) or (E) is not a small loss. Among all strict Scala programs there are two different functions into the one-element type `Unit` from any type: `_ => ()` returns, and `_ => loop()` does not. In Set there is exactly one function into a one-element set. Pairs misbehave too: `(1, loop())._1` never produces 1, although taking the first component of a pair should give back what was put there; chapter 18 shows that among all programs, pairs are not products but a weaker structure called restriction products, which describes exactly how divergence spreads. Lazy Haskell has the mirror-image problems, and its `seq` operator, which forces evaluation, can tell `undefined` apart from `\x -> undefined x`; that breaks even the identity law, which is Bauer's observation [Bauer 2016]. Among total programs all these problems disappear: `Nothing` is empty, `Unit` has exactly one function into it from any type, and tuples behave like pairs. Only the third choice keeps the properties that make types behave like sets.

#### The categorical version

Chapter 14 proves a sharper, purely categorical form of the theorem. In a category with products and function types, such as Set or 𝒮, an arrow from the one-element object to the empty object forces the two to be isomorphic, and then every hom-set has exactly one element. The category collapses. The expression z of (D) is precisely such an arrow. This is one instance of a family of results about categories with function types in which every endomorphism has a fixed point, which is what general recursion provides: such a category collapses if it also has coproducts or an initial object **[Standard: Huwig and Poigné 1990, checked (bibliographic entry and a survey's statement of the theorem)]**. It is why the categories of *domains* used to give meaning to general recursion lack an initial object in the usual sense **[Standard, from memory]**.

#### What the separation costs, and what it keeps

The way out taken in this document is not to forbid divergence but to keep two categories. 𝒮 contains only the total programs, so it has (E), (B) and no (D): reasoning in 𝒮 is reasoning about sets and functions. 𝒫 contains every program, so it has general recursion and loops, and gives up (B) as strict Scala does. Inside 𝒮 there is no general recursion. Recursion that terminates is still available there: structural recursion over data (folds, chapter 16) and recursion with a decreasing measure that Stainless can check. What is lost inside 𝒮 is the ability to write a function without knowing whether it terminates; such a function is an arrow of 𝒫, and chapters 18 and 19 show what can still be said about it.

### 2.6 Totality and equality, type by type

Two questions are still open. C2 says "applied to any argument, a function terminates", but what does that mean for an argument that is itself a function, which may or may not terminate when it is called? And Definition 2.2 quantifies over *all programs* with a hole, which is an infinite and wildly varied collection. To show that two functions are observationally equal you would have to consider every way any program could use them. That is hopeless as a proof method and useless as a testing method.

One definition answers both questions. It works by induction on types, and it defines which programs are total and when two total programs are equal at the same time.

**Definition 2.5 (total programs and their equality).** For every type A, define a relation s ≐ t between expressions of type A, read "s and t are equal total programs of type A", by induction on A, with expressions evaluated strictly:

- at a data type: s and t both terminate, and their results are equal by `===`;
- at a tuple type `(A, B)`: s and t both terminate, and their first components are related at A and their second components at B;
- at a function type `A -> B`: s and t both terminate, and s(a) ≐ t(a′) at B whenever a ≐ a′ at A.

An expression t of type A is **total** if t ≐ t. A function is total, in particular, when it sends total arguments to total results; what it does with a non-terminating argument is not asked, since under strict evaluation such an argument never reaches it.

For polymorphic types the definition needs relations between types as well as relations on values; that is the idea of chapter 9, and nothing in Part I depends on the details. The construction follows Danielsson and colleagues, who use such a relation to carve the total part out of a partial language [Danielsson et al. 2006, checked].

Three examples. `(n: BigInt) => n + 1` is total. `(n: BigInt) => if n > 0 then n else loop()` is not: applied to 0 it does not terminate. `(f: Int -> Int) => f(0)` is total, although it does not terminate when given a function that loops at 0: such a function is not total, so it is not one of the arguments the definition asks about.

**Proposition 2.6.** **[Proved]**

1. At every type, ≐ is symmetric and transitive. It is not reflexive: t ≐ t holds exactly when t is total.
2. For total expressions, observational equality implies ≐: if s and t are total and s ≈ t, then s ≐ t.

*Proof.* (1) By induction on the type. At data types, symmetry and transitivity of ≐ follow from those of `===`, and at tuple types from those of the components. At a function type, suppose f ≐ g and a ≐ a′. By induction a′ ≐ a, so f(a′) ≐ g(a) because f ≐ g, and by symmetry at B, g(a) ≐ f(a′); hence g ≐ f. For transitivity, suppose f ≐ g, g ≐ h and a ≐ a′. Then a ≐ a, by symmetry and transitivity at A, so f(a) ≐ g(a) and g(a) ≐ h(a′), hence f(a) ≐ h(a′). (2) By induction on the type. At data types this is the half of section 2.4 that was proved. At a function type, take a ≐ a′. The context "apply the hole to a" shows s(a) ≈ t(a); both are total because s and t are, so s(a) ≐ t(a) by induction. And t(a) ≐ t(a′) because t is total. By transitivity, s(a) ≐ t(a′). ∎

**What the definition buys.**

- **A definition of C2.** "Total" now has a precise meaning that does not refer to itself.
- **A proof method.** To prove two total functions equal, show that they agree on every total argument. Every proof of equality between total programs in this document works this way. The principle that functions are equal when they agree on every argument, often taken as an assumption about a language, is here simply the definition of equality in 𝒮.
- **A testing method.** To test two total functions for equality, apply them to many arguments and compare the results. If the results are themselves functions, apply them again. Eventually you compare data with `===`. This is concession 1, and Definition 2.5 says exactly which space the tests sample.

What the definition does not buy is decidability. There are still infinitely many arguments, and Proposition 2.1 shows that no program can check them all.

| Type | How s ≐ t is established |
| --- | --- |
| data type | compute `s === t` |
| tuple | establish ≐ for each component |
| `A -> B` | establish s(a) ≐ t(a) for every total a: by a proof for all a, or by tests for many a |

**What remains: assumption A1.** ≐ was defined without mentioning contexts. Proposition 2.6 connects it to observational equality in one direction. The other direction is the hard one, and it is assumed.

**Assumption A1 (fundamental lemma).** **[Assumed]** Every program of the language respects ≐: if s ≐ t and C is a context, then C[s] and C[t] either both fail to terminate or both terminate with equal results. In particular, equal total programs are observationally equal, even inside programs that are not total.

Why should A1 be true? Because of C3. Under the contract, the only operation a program can perform on a function value is to apply it. It can also store the function or pass it along, but sooner or later the only way to get information out of it is to apply it to something. A program that applies f only ever sees results f(a), and if those results are indistinguishable from the g(a), so is everything the program computes from them. Without C3, the argument collapses: a program could call `toString` on the function and learn its class name.

For model languages with recursion, statements of this kind are theorems, proved with logical relations like Definition 2.5 **[Standard: Pitts 2000, from memory]**, and Danielsson and colleagues prove the corresponding facts for their pair of languages [Danielsson et al. 2006, checked]. A1 has not been proved for Scala, which is why it is an assumption.

### 2.7 Strictness, laziness and recursion

Section 2.5 showed that strict and lazy evaluation fail in different ways when divergence is present. Does the choice matter for total programs?

**For equality in 𝒮, no.** If strict evaluation of a pure expression terminates, lazy evaluation of the same expression terminates with the same result **[Standard: Plotkin 1975, from memory]**. The converse fails, since lazy evaluation can skip a subexpression that strict evaluation would run forever, but that subexpression is then not total. So on total programs the two strategies agree; they differ only on programs that do not terminate somewhere, which are programs of 𝒫.

Three practical consequences follow.

- **By-name parameters, `lazy val`, and short-circuiting `&&`, `||` and `if`** do not change the meaning of total code. A by-name parameter of type `=> A` behaves like a parameter of type `A` when its argument is total.
- **Laziness can make code total that would otherwise not be.** `opt.getOrElse(sys.error("missing"))` is total exactly when `opt` is never empty, because `getOrElse` evaluates its argument only when needed. What matters is whether the code as written ever evaluates a divergent expression.
- **Infinite lazy data is a different matter.** A value such as `LazyList.from(0)` is an infinite structure. It can be produced without diverging, but many functions on it, such as `toList` or `length`, never terminate. Data types in the sense of section 2.2 are finite trees. Infinite structures are *codata*, and they need a different notion of totality, called productivity. Chapter 16 discusses them; they are outside the model of Part I.

**Recursion under strict evaluation.** General recursion produces programs of 𝒫, and strict evaluation decides where it can be used at all. A recursive definition is a **fixed point**: a value x with x = f(x) for a given f. The obvious way to compute one does not terminate under strict evaluation, for any f, because computing `fixNaive(f)` requires computing `fixNaive(f)` first:

```scala
def fixNaive[A](f: A -> A): A = f(fixNaive(f))
```

At function types there is a way out. A function value does not need its own result until it is applied, so the recursive reference can be delayed by wrapping it in a function literal, a step called **η-expansion**:

```scala
def fix[A, B](f: (A -> B) -> (A -> B)): A -> B =
  lazy val knot: A -> B = f(a => knot(a))
  knot

val factorial: BigInt -> BigInt = fix(rec => n => if n <= 0 then 1 else n * rec(n - 1))
```

Building `knot` terminates whenever `f` does, because the reference to `knot` inside `a => knot(a)` is only followed when the function is applied. So strict languages have fixed points at function types, and in general nowhere else. `fix` is a program of 𝒫: `fix(rec => rec)` builds a function that loops on every argument. `factorial` happens to be total, but that is a fact about this particular `f`, proved by induction on n; nothing in its type says so. Chapter 16 develops recursion on categories, and chapter 19 shows how *guarded* recursion, which only recurses after making progress, gives fixed points that are total.

**For performance, of course, the choice matters**, and the theory says nothing about it.

### 2.8 Two categories: 𝒫 and 𝒮

All the ingredients are now in place.

**Definition 2.7 (the category 𝒫).**

- **Objects**: the closed types of kind \* of the model. In Part I these are the data types and the types built from them with tuples and function types; Part II adds polymorphic types.
- **Arrows** A → B: values of type `A -> B` of the language fixed by C1 and C3, terminating or not, where observationally equal values are identified.
- **Identity** on A: `(a: A) => a`.
- **Composition** of f : A → B and g : B → C: `(a: A) => g(f(a))`.

**Definition 2.8 (the category 𝒮).**

- **Objects**: the same as those of 𝒫.
- **Arrows** A → B: total values of type `A -> B`, where values related by ≐ are identified. Strictly speaking, an arrow is an equivalence class of total function values. We name an arrow by any function value in its class.
- **Identity** and **composition**: as in 𝒫.

**Proposition 2.9.**

1. 𝒮 is a category. **[Proved]**
2. 𝒫 is a category. **[Standard: β-reduction of a function applied to a value is an observational equality under strict evaluation; Plotkin 1975, from memory]**
3. Sending each total function to itself is a functor from 𝒮 to 𝒫. It is faithful: different arrows of 𝒮 stay different in 𝒫. **[Proved, given A1]**

*Proof.* (1) First, composition is well defined on equivalence classes: if f ≐ f′ and g ≐ g′, then for a ≐ a′ we have f(a) ≐ f′(a′) and so g(f(a)) ≐ g′(f′(a′)), which is what `a => g(f(a))` ≐ `a => g′(f′(a))` means. The same argument shows that the composite of total functions is total, and the identity is total. Next, take f : A → B, g : B → C, h : C → D and a total argument a. Both `(h ∘ (g ∘ f))(a)` and `((h ∘ g) ∘ f)(a)` evaluate to h(g(f(a))), so the two composites agree on every total argument, and by Definition 2.5 they are equal. The identity laws follow in the same way, since `(id ∘ f)(a)` and `(f ∘ id)(a)` both evaluate to f(a). (3) A1 says that f ≐ g implies f ≈ g, so the functor is well defined on classes, and it preserves identities and composition because they are the same programs. Faithfulness is Proposition 2.6(2): total functions that are equal in 𝒫 are equal in 𝒮. ∎

Notice where each clause was used. C1 makes a function's result depend on its argument alone, so that comparing results is meaningful at all. C2 defines which programs are in 𝒮, and (1) needed nothing else: the proof is by Definition 2.5 alone. Only (3), the comparison with 𝒫, needed A1, and through it C3.

𝒮 is not a *full* subcategory of 𝒫: it has the same objects but fewer arrows, since 𝒫 also contains the programs that do not terminate. Chapter 18 shows that 𝒫 has more structure than a plain category. Every arrow of 𝒫 knows where it is defined, as an arrow of 𝒫 itself, which makes 𝒫 a **restriction category**, and the arrows that are defined everywhere are exactly those of 𝒮 **[Standard: Cockett and Lack 2002, checked (bibliographic entry)]**. Categories of this kind, with enough structure to describe a universal machine, are the categorical account of computability **[Standard: Cockett and Hofstra, Turing categories, from memory]**.

**𝒮 and 𝒫 in code.** In this document and in the library, the arrows of 𝒮 have the pure function type `A -> B`. Writing a value of that type and using it as an arrow is the assertion of C2. Programs that may not terminate get their own type, so that the assertion is never made by accident, and their own arrow, `A ~> B`. Here is the shape the library gives it:

```scala
opaque type Partial[A, B] = A -> B
type ~> = Partial

object Partial:
  /** A program that may not terminate. Applied to an arrow of 𝒮, this is the functor 𝒮 → 𝒫. */
  def apply[A, B](f: A -> B): A ~> B = f

  /** Asserts that p terminates on every total argument, which makes it an arrow of 𝒮. */
  def assumeTotal[A, B](p: A ~> B): A -> B = p

val search: BigInt ~> BigInt = Partial(n => fix[BigInt, BigInt](rec => k => if k * k >= n then k else rec(k + 1))(0))
```

`search` finds the least k with k² ≥ n by counting up, which terminates for every n; but nothing checked that, so it is written as a program of 𝒫. Turning it into an arrow of 𝒮 requires `Partial.assumeTotal(search)`, and that call is the promise. Searching the code for `assumeTotal` finds every place where the promise is made; that is the sense in which the library makes concession 3 explicit.

Two axes are now separate. `->` versus `=>` is purity, C1, and the compiler checks it. 𝒮 versus 𝒫 is totality, C2, and the programmer asserts it. Both categories contain only pure programs; functions of type `A => B`, which may have effects, are arrows of neither.

**Scope.** Scala has many features these definitions do not mention: subtyping, variance, implicit conversions, match types, singleton types and more. Code may use them, but unless a chapter says otherwise, the theory in this document says nothing about them. Chapter 21 collects the features that lie outside the model.

### 2.9 Does the syntax of programs matter?

𝒮 is built out of programs, so it is natural to ask how much it depends on the way those programs are written.

**The syntax of individual programs does not matter.** An arrow is an equivalence class of programs. Two programs that are written completely differently but agree on every total argument, such as `x => x + x` and `x => 2 * x` on `Int`, are the same arrow. No law and no theorem of this document can see the difference.

**The language as a whole matters, in two ways.**

1. *Which programs exist* determines which arrows exist. Remove a feature that some arrows need and those arrows disappear.
2. *Which observations exist* determines ≈. Add `eq` to the allowed programs and arrows that were equal split apart, as section 2.3 showed. Remove a way of observing and arrows that were different may merge.

So 𝒮 is a construction on the language, not on its syntax. Category theorists call a category built this way, with terms of a language as arrows up to some equivalence, a **syntactic category** or **term model** **[Standard: Lambek and Scott 1986, from memory]**. The alternative is a **semantic** construction, in which types are interpreted as mathematical objects, such as sets, and programs as functions between them.

Definition 2.5 connects the two views: an arrow A → B of 𝒮 is determined by what it does to total values. Section 2.10 shows that this makes 𝒮 a faithful copy of a part of Set. For first-order types, such as functions from `BigInt` to `BigInt`, that part is robust. Every total computable function on data is an arrow of 𝒮, because Scala can compute it and the program that computes it is then total **[Standard: the Church–Turing thesis]**. This depends on how 𝒮 was built: as the total part of a language that can also express programs that do not terminate. A language that is total by construction cannot compute every total computable function, since it cannot contain an interpreter for itself (chapter 16 gives the diagonal argument) **[Standard, from memory]**. For higher-order types, the language matters even semantically. Which functions that take functions as arguments can be defined depends on the language: a sequential language cannot define the "parallel or" of Plotkin's PCF, for example **[Standard: Plotkin 1977, from memory]**. So 𝒮 is determined by Scala's expressive power at every type, and not by the surface form of any particular program.

### 2.10 𝒮 and Set: faithful, but not full

How does 𝒮 compare with Set? To compare two categories, use a functor (section 1.4).

**The functor Val.** For a type A, let Val(A) be the set of total values of A, with values related by ≐ identified. For an arrow f : A → B, let Val(f) : Val(A) → Val(B) be the function "apply f". Then Val is a functor from 𝒮 to Set: applying the identity function does nothing, and applying a composite is applying one function after the other. **[Proved]**

Val is the bridge between the two worlds. Section 1.4 explained what faithfulness and fullness would tell us: faithfulness means equations can be checked in Set, and fullness means constructions in Set give programs. So these are the right questions to ask.

**Proposition 2.10 (Val is faithful).** **[Proved]** If Val(f) = Val(g), then f(a) ≐ g(a) for every total value a, so f ≐ g by Definition 2.5.

*Meaning.* To prove that two programs are equal, it suffices to prove that the functions they compute are equal as functions between sets. Everything you know about functions, every equation of ordinary mathematics, can be used to prove equations between programs. This is what justifies reasoning about Scala code with pencil-and-paper mathematics.

**Proposition 2.11 (Val is not full).** **[Standard: Turing]** Number all Scala programs 0, 1, 2, …, and let h : Val(BigInt) → Val(Boolean) send n to `true` when n ≥ 0 and program number n halts, and to `false` otherwise. This is a perfectly good function between sets, but no program computes it, because the halting problem is undecidable.

*Meaning.* A construction in Set does not, in general, give a program. If a mathematical argument proves that some function *exists*, Scala may have no such function. Existence does not transfer from Set to 𝒮.

**Proposition 2.12 (finite types agree).** **[Proved]** If Val(A) and Val(B) are finite, then every function Val(A) → Val(B) is Val(f) for some arrow f. Write f as a lookup table: one `match` case per value of A, in principle. For `Int`, with its 2³² values, the table is absurdly large, but it exists. So for finite types, Val is full.

**Proposition 2.13 (countable homs).** **[Standard: Cantor]** For every A and B there are only countably many arrows A → B in 𝒮, because programs are finite strings. If Val(A) is infinite, Set has uncountably many functions Val(A) → Val(Boolean). So for every infinite type A, all but a countable part of Set's functions Val(A) → Val(Boolean) are missing from 𝒮. In the sense of cardinality, 𝒮 contains almost none of them.

| | Set | 𝒮 |
| --- | --- | --- |
| Objects | all sets | the closed types of the model |
| Arrows A → B | all functions | total function values, up to ≐ |
| Equality of arrows | equality of functions | ≐: agreement on every total argument (Definition 2.5) |
| Equality of arrows decidable? | not a meaningful question | no (Proposition 2.1) |
| Functions between finite types | all of them | all of them (Proposition 2.12) |
| Functions from ℕ to {true, false} | uncountably many | countably many: the computable ones |
| Relationship | — | Val : 𝒮 → Set is faithful but not full |

So the answer to "is the category of programs Set?" has two parts. Without a contract, there is no category of programs that behaves like Set at all. With one, Val maps 𝒮 into Set without losing any distinctions, so equational reasoning in Set is sound for total programs. But Val reaches only the computable part of Set, so existence claims do not transfer. Part II shows further differences, concerning subsets and quotients, and chapter 9 shows something 𝒮 has that Set lacks: polymorphism with free theorems.

### 2.11 Fast and loose reasoning, and the totality promise

Scala as a whole is not total, and we reason about the total part of it. That this is sound in principle has been shown for a model language. Danielsson, Hughes, Jansson and Gibbons define two small functional languages with identical syntax, one total and one partial [Danielsson et al. 2006, checked]. In the partial language, a relation picks out the total values: it relates equal values at data types, and relates functions that send related arguments to related results, as Definition 2.5 does. They prove that if two closed terms are equal in the total language, they are related in the partial language, and that the total values form a category with products, coproducts and function types. Their title, *Fast and Loose Reasoning is Morally Correct*, names the method: reasoning that ignores non-termination is sound for the parts of the program that terminate.

Their theorem is about their pair of languages, not about Scala, and no corresponding theorem is known for Scala **[Open]**. It is still the clearest model of what this document does. 𝒮 is carved out of the partial language exactly as they carve out the total values, and concession 3 is now precise: the programmer asserts that a program is a member of 𝒮. Stainless can check the assertion for code in its subset; elsewhere, the library confines the assertion to the uses of `Partial.assumeTotal` and to the values written with type `A -> B`.

### 2.12 Set and Scala

In Set, equality of functions is simply equality of outputs, every function exists, and the empty set is empty without conditions. In Scala, each of these has to be earned. All programs together form 𝒫, where equality is observational equality and substitution fails as soon as an argument may not terminate. The total programs form 𝒮, where equality is agreement on every total argument, by definition; it can be proved for all arguments or tested on many, but never decided by a program. The empty type is empty and substitution holds in 𝒮 only because 𝒮 contains no divergence, and Theorem 2.4 shows that no category of programs can have divergence, substitution and an empty type at once. And only the computable functions exist. In return, the functor Val is faithful, so the mathematics of functions can be used to reason about total programs.

| Question | Set | 𝒮 | 𝒫 |
| --- | --- | --- | --- |
| Is it a category? | yes, unconditionally | yes (Proposition 2.9) | yes (Proposition 2.9) |
| What does "f = g" mean? | same output on every input | same results on every total argument (≐) | no program can tell them apart (≈) |
| How is it checked? | by proof | by proof for all arguments, or by tests on many | by proof; tests that stop cannot observe divergence |
| Does substitution (B) hold? | yes | yes | only for arguments that are values |
| Is the empty type empty? | yes | yes | yes, but `(_: Nothing) => 1` can still be applied to a loop |
| Does every function exist? | yes | only total computable ones; all of them between finite types | only computable ones, possibly partial |

### Addendum 2.A: `Option` and `PartialFunction`

C2 asks for total functions, and section 2.3 recommended `Option` for functions that may fail. Scala also has `PartialFunction[A, B]`, which seems designed for exactly this situation. How do the two compare?

A `PartialFunction[A, B]` is a function that comes with a predicate `isDefinedAt: A => Boolean`. Applying it to an argument outside its domain throws a `MatchError`. So `pf.apply`, used as an arrow, breaks C2 on every argument outside the domain; it is at best an arrow of 𝒫, failing by an exception rather than by looping. The domain is described by a predicate, which means it is a *subset* of `A`, not a type. Chapter 6 shows why subsets cause trouble for categories in Scala.

`Option` takes the opposite approach. A function `A -> Option[B]` is total: it answers every argument, and the answer says whether a result exists. The domain is no longer a separate subset; it is encoded in the result type. The two are interconvertible: `pf.lift` turns a partial function into an `A => Option[B]`, and `Function.unlift` turns one back. Mathematically, partial functions between sets form a category whose composite is defined wherever both parts are, and this category is equivalent to the category of functions `A → Option(B)` with Kleisli composition **[Standard, from memory]**. Chapter 3 builds the Scala version of that category, `OptionKleisli`. Chapter 18 compares the two ways of being partial in Scala: 𝒫, whose failures cannot be detected by the program, and the Kleisli category of `Option`, whose failures are values that a program can inspect.

So, under the contract: use `A -> Option[B]` (or `Either`) for arrows of 𝒮. Use `PartialFunction` only through `lift` or `applyOrElse`, which are total. Relying on `isDefinedAt` before calling `apply` is a convention that nothing checks, and it evaluates the pattern match twice.

### References for chapter 2

**Consulted while writing this chapter**

- Andrej Bauer, "Hask is not a category", *Mathematics and Computation* (blog), August 6, 2016. https://math.andrej.com/2016/08/06/hask-is-not-a-category/
- HaskellWiki, "Hask". https://wiki.haskell.org/Hask
- Nils Anders Danielsson, John Hughes, Patrik Jansson and Jeremy Gibbons, "Fast and Loose Reasoning is Morally Correct", *POPL 2006*, pp. 206–217. https://www.cse.chalmers.se/~nad/publications/danielsson-et-al-popl2006.html
- H. Huwig and A. Poigné, "A note on inconsistencies caused by fixpoints in a cartesian closed category", *Theoretical Computer Science* 73(1), 1990, pp. 101–112. (Bibliographic entry and a survey's statement of the main theorem consulted; the paper itself was not.)
- J. R. B. Cockett and S. Lack, "Restriction categories I: categories of partial maps", *Theoretical Computer Science* 270, 2002. (Bibliographic entry only.)
- Scala 3 reference, version 3.10.0: "Tracked Capabilities Overview", https://scala-lang.org/api/3.x/docs/experimental/capture-checking/overview.html; "Safe Mode", https://scala-lang.org/api/3.x/docs/experimental/capture-checking/safe.html; "The Matchable Trait", https://scala-lang.org/api/3.x/docs/other-new-features/matchable.html
- Scala 3 reference: "Multiversal Equality", https://scala-lang.org/api/docs/contextual/multiversal-equality.html; "Better Support for Type Classes", https://scala-lang.org/api/docs/experimental/typeclasses.html
- VirtusLab, "Introduction to Scala 3's Capture Checking and Separation Checking" (blog). https://virtuslab.com/blog/scala/introduction-to-scala-3-checking
- Stainless repository README. https://github.com/epfl-lara/stainless
- Viktor Kunčak, talk abstract "Stainless", Lambda Days 2020. https://lambdadays.org/lambdadays2020/viktor-kunak/
- An older version of Stainless's "Pure Scala" documentation. https://github.com/flonso/stainless/blob/master/core/src/sphinx/purescala.rst
- The behavior of capture checking and separation checking on local mutable variables was checked with the Scala 3.10.0 compiler.

**Cited from memory, not consulted**

- Gordon Plotkin, "Call-by-name, call-by-value and the λ-calculus", *Theoretical Computer Science* 1, 1975.
- Andrew M. Pitts, "Parametric polymorphism and operational equivalence", *Mathematical Structures in Computer Science* 10, 2000.
- Gordon Plotkin, "LCF considered as a programming language", *Theoretical Computer Science* 5, 1977.
- J. Lambek and P. J. Scott, *Introduction to Higher Order Categorical Logic*, Cambridge University Press, 1986.
- J. R. B. Cockett and P. J. W. Hofstra, "Introduction to Turing categories", *Annals of Pure and Applied Logic* 156, 2008.
- The undecidability of the halting problem (Turing), Cantor's diagonal argument, the Church–Turing thesis, and uniqueness types in Clean.

---

## Chapter 3. Defining your own category

### 3.1 The idea

To define a category you make four choices and check three laws. You choose the objects, the arrows between any two objects, the identity arrows, and how arrows compose. Then you check associativity and the two identity laws.

In Scala, the usual way to make these choices is to let the objects be types and to pick a type constructor whose values `Self[A, B]` are the arrows from `A` to `B`. Identity and composition are then polymorphic functions. This chapter shows how that is done, how the laws are stated and checked, and how much freedom there is in choosing the objects. Chapter 4 explains what the choice commits you to.

### 3.2 Why programmers care

Many things that compose are not plain functions. A function that may fail, `A -> Option[B]`, composes by stopping at the first failure. A function that also produces a log composes by concatenating logs. A lens, which focuses on part of a data structure, composes by focusing deeper. Parsers, state-machine transitions, database migrations and linear maps all compose in their own ways.

Each of these is a category, provided its composition satisfies the laws. Once you know that, every generic tool written against the category interface works for it. Section 3.9 gives one such tool, an algorithm whose correctness depends on nothing but the laws.

### 3.3 The interface

A category's laws are equations between arrows, so before the interface itself we need a way to check an equation between arrows. Chapter 2 defined the equality: for arrows of 𝒮, agreement on every total argument. Proposition 2.1 showed that no program can decide it. What a program *can* do is compare finitely many observations of two arrows, each ending in data that `===` compares. That is a test, not a decision, and it gets its own type class:

```scala
import tutorial.ch02.Snippets.Eq
import Eq.given

trait Observable extends caps.Pure:
  type Self
  /** Returns false only if some observation tells a and b apart. */
  def agree(a: Self, b: Self): Boolean
  extension (a: Self) def =?=(b: Self): Boolean = agree(a, b)

object Observable:
  /** Data observes itself. */
  given EqIsObservable: [A: Eq] => A is Observable:
    def agree(a: A, b: A): Boolean = a === b

  /** Observes a value through finitely many observations. */
  def through[A, O: Observable](observations: List[A -> O]): A is Observable = new Observable:
    type Self = A
    def agree(a: A, b: A): Boolean = observations.forall(o => o(a) =?= o(b))

  /** Observes a function by applying it at sample points. */
  def function[A, B: Observable](points: List[A]): (A -> B) is Observable =
    through[A -> B, B](points.map(a => (f: A -> B) => f(a)))
```

Three facts make `Observable` the right tool, and one fact limits it.

- **It is sound for refutation.** If two total functions are equal, they agree at every sample point, so `Observable.function(points)` never reports a difference between equal functions. A law that fails under some `Observable` is false. **[Proved, from Definition 2.5]**
- **It is an equivalence relation**, whenever the equality of its observations is one. **[Proved]**
- **It is deterministic and pure.** The sample points are chosen by whoever constructs the instance, and a test chooses them afresh for every property it checks (section 3.10). Randomness belongs to the generator of sample points, never to the comparison.
- **It is not a congruence**: two arrows that agree on the samples, composed with two others that agree on the samples, can give composites that disagree. Section 5.2 gives an example. So a law whose premise is "these two arrows are equal" cannot be checked by sampling the premise.

The library states the first two facts as laws of `Observable` itself, in `ObservableLaws`: reflexivity, symmetry and transitivity, and **soundness**, which says that two values equal by construction, such as a function and its η-expansion, agree. For the constructions above they are proved; the tests check them for every observation that the other law tests use, and record the failure of congruence as a counterexample.

Here is the interface, with its laws stated inside it:

```scala
abstract class Category extends caps.Pure:
  type Self[_, _]
  final type -->[A, B] = Self[A, B]

  def identity[A]: A --> A
  def compose[A, B, C](g: B --> C, f: A --> B): A --> C

  extension [A, B](f: A --> B) def >>>[C](g: B --> C): A --> C = compose(g, f)

  /** An isomorphism (section 1.3): two arrows, inverse by the law `isomorphism`. */
  final case class Iso[A, B](to: A --> B, from: B --> A)

  // Laws. Each must return true for all arrows, under every observation.
  object CategoryLaws:
    def leftIdentity[A, B](f: A --> B)(using (A --> B) is Observable): Boolean =
      (f >>> identity[B]) =?= f

    def rightIdentity[A, B](f: A --> B)(using (A --> B) is Observable): Boolean =
      (identity[A] >>> f) =?= f

    def associativity[A, B, C, D](f: A --> B, g: B --> C, h: C --> D)(using (A --> D) is Observable): Boolean =
      ((f >>> g) >>> h) =?= (f >>> (g >>> h))

    /** Premise, not checked: f2 equals f and g2 equals g. */
    def congruence[A, B, C](f: A --> B, f2: A --> B, g: B --> C, g2: B --> C)(
        using (A --> C) is Observable): Boolean =
      (f >>> g) =?= (f2 >>> g2)

    def isomorphism[A, B](i: Iso[A, B])(using (A --> A) is Observable, (B --> B) is Observable): Boolean =
      ((i.to >>> i.from) =?= identity[A]) && ((i.from >>> i.to) =?= identity[B])
```

`Self` is the type constructor of arrows, and `-->` is a more descriptive name for it: `A --> B` is the type of arrows from `A` to `B`. `compose(g, f)` is g ∘ f, in mathematical order, so its first argument is applied last. Code reads more easily in the order the arrows run, so the class also provides `f >>> g`, which is the same composite written diagrammatically: f first, then g. This document writes ∘ in mathematics and `>>>` in code. `extends caps.Pure` declares the category itself pure, as section 2.2 did for `Eq`.

A category is a value. An instance is an object that extends `Category`, and generic code takes the category as a parameter, as section 3.9 shows.

**Why the laws take an `Observable`.** Each law is an equation between two arrows. The law method cannot decide that equation, so it checks it through the `Observable` it is given: the law returns `true` when the two sides agree on every observation. A failed check is a genuine counterexample, because `Observable` is sound for refutation. A passed check is evidence, not proof. The same Boolean method serves both ways of establishing a law. A test constructs an `Observable` with sample points and checks that the method returns `true` (concession 1). A proof shows that the two sides are equal, which implies that the method returns `true` under every `Observable` built from total observations. Section 3.10 does both.

**Congruence.** The law `congruence` says that composition does not depend on which representative of an arrow we hold: equal arrows composed give equal composites. For the functions of 𝒮 it holds by Definition 2.5, as the proof of Proposition 2.9 showed. Chapter 7 meets categories where it is a real obligation. Its premise is an equation between arrows, which sampling cannot establish, so the premise is not checked: a test passes arrows that are equal *by construction*, called **variants**, such as `f` and `x => f(x)`.

**Should the laws be inside the class?** Keeping them there has four advantages.

1. The laws are part of what the type class means; a `Category` without its laws is just two functions. Putting them next to `identity` and `compose` makes the obligation visible exactly where an instance is written.
2. A law is called on the instance, as in `K.CategoryLaws.associativity(...)`, so nothing has to pass the instance around separately.
3. It matches Stainless's design, in which laws are declared in the abstract structure and proved for each instance (section 2.3).
4. An instance cannot redefine a law: the object `CategoryLaws` is not a member it can override.

There are costs. The law methods become members of every instance at run time, which is harmless since production code never calls them. The laws need equality on observations, so `Eq` and `Observable` become dependencies of `Category`. And a law with a premise, such as congruence, is checked only for inputs that satisfy the premise by construction.

### 3.4 Example: functions

The category 𝒮 of chapter 2, as an instance:

```scala
object Total extends Category:
  type Self[A, B] = A -> B
  def identity[A]: A -> A = a => a
  def compose[A, B, C](g: B -> C, f: A -> B): A -> C = a => g(f(a))
```

The name says what its arrows are: total programs, as opposed to the programs of 𝒫, which the code calls `Partial`. Its arrows have the pure function type, so capture checking checks C1 for every arrow that enters the category. Totality, C2, is asserted: using a value of `A -> B` as an arrow of `Total` is the assertion. The laws were proved in Proposition 2.9. The library's 𝒮 is this object, under the same name.

### 3.5 Example: functions that may fail

Functions `A -> Option[B]` compose by stopping at the first `None`:

```scala
object OptionKleisli extends Category:
  type Self[A, B] = A -> Option[B]
  def identity[A]: A -> Option[A] = a => Some(a)
  def compose[A, B, C](g: B -> Option[C], f: A -> Option[B]): A -> Option[C] =
    a => f(a).flatMap(g)
```

This is the honest form of a partial function (Addendum 2.A). Instead of breaking C2 by throwing on bad input, the function says in its type that it may produce no result:

```scala
final case class User(id: Int, name: String) derives CanEqual

val users: Map[Int, User] = Map(1 -> User(1, "Ada"), 2 -> User(2, "Grace"))

val parse: String -> Option[Int] = _.toIntOption
val positive: Int -> Option[Int] = n => if n > 0 then Some(n) else None
val lookup: Int -> Option[User]  = users.get

val findUser: String -> Option[User] =
  import OptionKleisli.>>>
  parse >>> positive >>> lookup
```

The import selects which category's `>>>` is meant: an arrow `A -> Option[B]` of `OptionKleisli` is also an arrow `A -> Option[B]` of `Total`, where `>>>` would mean something else.

**Proposition 3.1.** `OptionKleisli` is a category. **[Proved]**

*Proof.* By Definition 2.5 it suffices to check each law at an arbitrary total argument a. All three checks are case analyses.

- *Left identity.* `compose(identity, f)(a)` is `f(a).flatMap(Some(_))`. If `f(a)` is `None`, this is `None`; if it is `Some(b)`, this is `Some(b)`. In both cases it equals `f(a)`.
- *Right identity.* `compose(f, identity)(a)` is `Some(a).flatMap(f)`, which is `f(a)`.
- *Associativity.* The left side `compose(h, compose(g, f))(a)` is `f(a).flatMap(b => g(b).flatMap(h))`. The right side `compose(compose(h, g), f)(a)` is `f(a).flatMap(g).flatMap(h)`. If `f(a)` is `None`, both are `None`. If `f(a)` is `Some(b)`, both are `g(b).flatMap(h)`. ∎

The case analysis considered only `None` and `Some`, which is valid because C3 excludes `null`. Categories of this shape, with arrows `A -> T[B]` for some type constructor `T`, are called **Kleisli categories**. Chapter 15 shows that every monad gives one, and the library's `Kleisli.OptionKleisli` is this category built that way.

### 3.6 Example: lenses

A lens from `S` to `A` lets you read an `A` out of an `S` and write a new `A` back into it:

```scala
final case class Lens[S, A](get: S -> A, set: (S, A) -> S)

object Lenses extends Category:
  type Self[A, B] = Lens[A, B]
  def identity[A]: Lens[A, A] = Lens(a => a, (_, a) => a)
  def compose[A, B, C](g: Lens[B, C], f: Lens[A, B]): Lens[A, C] =
    Lens(
      a => g.get(f.get(a)),
      (a, c) => f.set(a, g.set(f.get(a), c))
    )
```

Composition focuses deeper. To set the inner part, read the middle part, set the inner part inside it, and write the middle part back:

```scala
final case class Address(street: String, city: String) derives CanEqual
final case class Person(name: String, address: Address) derives CanEqual

val address: Lens[Person, Address] = Lens(_.address, (p, a) => p.copy(address = a))
val city: Lens[Address, String]    = Lens(_.city, (a, c) => a.copy(city = c))

val personCity: Lens[Person, String] =
  import Lenses.>>>
  address >>> city
```

`Lens` deliberately does not derive `CanEqual`: its fields are functions, and `==` on it would compare them by reference. Two lenses are equal when their `get` functions are equal and their `set` functions are equal, so the natural observation of a lens at a state `s` and a new value `x` is the pair `(l.get(s), l.set(s, x))`:

```scala
def lenses[S: Eq, A: Eq](points: List[(S, A)]): Lens[S, A] is Observable =
  Observable.through(points.map((s, x) => (l: Lens[S, A]) => (l.get(s), l.set(s, x))))
```

**Proposition 3.2.** `Lenses` is a category. **[Proved]**

*Proof.* For both sides of the associativity law, `get` is `a => h.get(g.get(f.get(a)))`. Unfolding the definitions, both `set` functions send `(a, d)` to

f.set(a, g.set(f.get(a), h.set(g.get(f.get(a)), d))).

For the identity laws, `compose(identity, f)` and `compose(f, identity)` both have `get` equal to `f.get` and `set` equal to `(a, c) => f.set(a, c)`. ∎

Notice what the proof did not use. Practitioners expect a lens to satisfy three **lens laws**: reading what you just wrote gives it back, writing what you just read changes nothing, and a second write overwrites the first. The proof never mentioned them. `Lens[S, A]` is the type of *all* get/set pairs, lawful or not. For example, `Lens[Int, Int](_ => 0, (s, _) => s + 1)` is a perfectly good value of the type and violates all three laws.

Composites of lawful lenses are lawful **[Standard, from memory; each law of the composite reduces to the same law for the two parts]**, so mathematically the lawful lenses form a category of their own inside this one. But "lawful" is not a type. There is no way to write a type of "lenses from A to B that satisfy the lens laws" in Scala. This is the first concrete instance of a theme of chapter 4, and chapter 6 is devoted to it.

### 3.7 New categories from old: the opposite category

Some constructions turn any category into another. The simplest reverses every arrow.

**Definition 3.3.** The **opposite** of a category 𝒞, written 𝒞ᵒᵖ, has the same objects as 𝒞, an arrow a → b for every arrow b → a of 𝒞, the same identities, and composition in the reverse order.

```scala
def opposite(K: Category): Category { type Self[A, B] = K.Self[B, A] } = new Category:
  type Self[A, B] = K.Self[B, A]
  def identity[A]: K.Self[A, A] = K.identity[A]
  def compose[A, B, C](g: K.Self[C, B], f: K.Self[B, A]): K.Self[C, A] = K.compose(f, g)
```

`opposite` takes a category as an ordinary parameter and returns a new one. Its result type records what `Self` is, so the arrows of `opposite(Total)` are known to be functions in the reverse direction. The library makes the opposite a member, `K.op`.

The laws of `opposite(K)` are the laws of `K` read backwards **[Proved]**: the associativity law of the opposite for f, g, h is the associativity law of `K` for h, g, f, and the two identity laws swap. Every concept of category theory has a dual obtained by passing to the opposite, and the opposite of `Total` is where *contravariance* comes from: chapter 12 shows that a function that consumes values, such as a predicate or a comparator, is naturally an arrow of the opposite of `Total`.

Other constructions of this kind appear throughout the document. A Kleisli category keeps the objects and changes the arrows. A **subcategory** keeps some of the objects and some of the arrows, and a **full subcategory** keeps some of the objects and all the arrows between them. Section 3.8 shows how to keep fewer objects.

### 3.8 Objects

The definition of a category starts with "a collection of objects", yet the `Category` class so far never mentions objects. They are implicit in the type parameters. `identity[A]` promises an identity arrow for every type `A` of kind \*, so the objects of every `Category` instance are *all* the types of kind \*. This section asks how much freedom that leaves, and how to get more.

#### Isomorphic objects, in code

An isomorphism between two objects is a pair of arrows that compose to identities (section 1.3). In code, the pair is data, `Iso`, and the condition is the law `isomorphism`. In `Total`, swapping the components of a pair is an isomorphism `(A, B) ≅ (B, A)`, and it is its own inverse:

```scala
def swap[A, B]: Total.Iso[(A, B), (B, A)] = Total.Iso(_.swap, _.swap)
```

Less obviously, `Option[Nothing] ≅ Unit`:

```scala
val noneIsUnit: Total.Iso[Option[Nothing], Unit] = Total.Iso(_ => (), _ => None)
```

Going from `Unit` to `Option[Nothing]` and back is clearly the identity. Going from `Option[Nothing]` to `Unit` and back sends every value to `None`, which is the identity only because `None` is the *only* total value of `Option[Nothing]`. **[Proved]** Isomorphisms like this one are statements about what values a type has, and they depend on the contract.

#### Restricting the objects with evidence

Sometimes a category should have fewer objects. Relations need to search the middle object, so they need objects whose values can be listed (chapter 8). A category of sets represented as lists needs to compare elements, so it needs objects with an `Eq` (chapter 7). A monoid should be a category with exactly one object (section 1.2). In each case, being an object comes with information that the category's programs need.

The way to say this in Scala is to require **evidence** that a type is an object. The category names a type class, `Obj`, and a type `A` is an object exactly when an instance `A is Obj` can be found. Identity and composition take the evidence of their objects as context bounds, so they can use it. One type class has an instance for every type, which gives back the categories of the previous sections:

```scala unit=Categories
/** Evidence that every type has. */
trait Type extends caps.Pure:
  type Self

object Type:
  given TIsType: [T] => T is Type {}

abstract class Category extends caps.Pure:
  type Self[_, _]
  final type -->[A, B] = Self[A, B]

  /** The type class selecting the objects: a type A is an object when `A is Obj` can be found. */
  type Obj <: Type

  def identity[A: Obj]: A --> A
  def compose[A: Obj, B: Obj, C: Obj](g: B --> C, f: A --> B): A --> C

  extension [A: Obj, B: Obj](f: A --> B) def >>>[C: Obj](g: B --> C): A --> C = compose(g, f)

  final case class Iso[A, B](to: A --> B, from: B --> A)

  object CategoryLaws:
    def leftIdentity[A: Obj, B: Obj](f: A --> B)(using (A --> B) is Observable): Boolean =
      (f >>> identity[B]) =?= f

    def rightIdentity[A: Obj, B: Obj](f: A --> B)(using (A --> B) is Observable): Boolean =
      (identity[A] >>> f) =?= f

    def associativity[A: Obj, B: Obj, C: Obj, D: Obj](f: A --> B, g: B --> C, h: C --> D)(
        using (A --> D) is Observable): Boolean =
      ((f >>> g) >>> h) =?= (f >>> (g >>> h))

    /** Premise, not checked: f2 equals f and g2 equals g. */
    def congruence[A: Obj, B: Obj, C: Obj](f: A --> B, f2: A --> B, g: B --> C, g2: B --> C)(
        using (A --> C) is Observable): Boolean =
      (f >>> g) =?= (f2 >>> g2)

object Total extends Category:
  type Self[A, B] = A -> B
  type Obj        = Type
  def identity[A: Type]: A -> A = a => a
  def compose[A: Type, B: Type, C: Type](g: B -> C, f: A -> B): A -> C = a => g(f(a))
```

`Obj <: Type` says that whatever type class selects the objects must be a kind of `Type`. For an evidence class to qualify, it extends `Type`, and that applies to `Eq`: in the library, `Eq` extends `Type`, so that "the types with an equality" can be the objects of a category. Here are `Eq` and `Observable` again in that form, with the instances the rest of the document needs and the laws of section 2.2 left out:

```scala unit=Categories
trait Eq extends Type:
  def equal(a: Self, b: Self): Boolean
  extension (a: Self) def ===(b: Self): Boolean = equal(a, b)

object Eq:
  def structural[A](using CanEqual[A, A]): A is Eq = new Eq:
    type Self = A
    def equal(a: A, b: A): Boolean = a == b

  given IntIsEq: (Int is Eq)         = structural
  given BooleanIsEq: (Boolean is Eq) = structural
  given StringIsEq: (String is Eq)   = structural
  given UnitIsEq: (Unit is Eq)       = structural
  given BigIntIsEq: (BigInt is Eq) =
    given CanEqual[BigInt, BigInt] = CanEqual.derived
    structural

  given OptionIsEq: [A: Eq] => Option[A] is Eq:
    def equal(a: Option[A], b: Option[A]): Boolean = (a, b) match
      case (Some(x), Some(y)) => x === y
      case (None, None)       => true
      case _                  => false

  given Tuple2IsEq: [A: Eq, B: Eq] => (A, B) is Eq:
    def equal(a: (A, B), b: (A, B)): Boolean = a._1 === b._1 && a._2 === b._2

  given ListIsEq: [A: Eq] => List[A] is Eq:
    def equal(a: List[A], b: List[A]): Boolean =
      a.length == b.length && a.lazyZip(b).forall((x, y) => x === y)

import Eq.given

trait Observable extends caps.Pure:
  type Self
  def agree(a: Self, b: Self): Boolean
  extension (a: Self) def =?=(b: Self): Boolean = agree(a, b)

object Observable:
  given EqIsObservable: [A: Eq] => A is Observable:
    def agree(a: A, b: A): Boolean = a === b

  def through[A, O: Observable](observations: List[A -> O]): A is Observable = new Observable:
    type Self = A
    def agree(a: A, b: A): Boolean = observations.forall(o => o(a) =?= o(b))

  def function[A, B: Observable](points: List[A]): (A -> B) is Observable =
    through[A -> B, B](points.map(a => (f: A -> B) => f(a)))
```

These are the definitions of the library's `Type`, `Eq`, `Observable` and `Category`, apart from the members this document has not yet needed; the rest of the document uses them. Now the objects can be restricted. Restricting a category to the types with some evidence, and keeping all arrows between them, gives a full subcategory. For example, `Total` restricted to the types with an `Eq` is the category of types with decidable equality, which is useful whenever an arrow needs to compare its inputs:

```scala unit=Categories
def withEq(K: Category { type Obj = Type }): Category { type Self[A, B] = K.Self[A, B]; type Obj = Eq } =
  new Category:
    type Self[A, B] = K.Self[A, B]
    type Obj        = Eq
    def identity[A: Eq]: K.Self[A, A] = K.identity[A]
    def compose[A: Eq, B: Eq, C: Eq](g: K.Self[B, C], f: K.Self[A, B]): K.Self[A, C] = K.compose(g, f)

val TotalWithEq = withEq(Total)
```

Inside `withEq`, `K.identity[A]` needs evidence that `A` is a `Type`, and the evidence that `A` has an `Eq` serves, because `Eq` extends `Type`. That convenience has a side effect worth knowing. A query for `A is Type` can now be answered either by the instance `TIsType` or by any `Eq` instance in scope, so the evidence found for an object is not always the same value. For `Type`, which has no members, this cannot matter. For a type class with members it can, and chapter 7 meets the case.

Notice also that `withEq` returns an ordinary value, not a given. A category is a first-class **module**: it can be stored, passed and returned, and its types are referred to through it, as in `TotalWithEq.-->[Int, String]`.

#### Monoids, two ways

A monoid is a one-object category (section 1.2). Here is the type class, with its laws:

```scala unit=Categories
trait Monoid extends caps.Pure:
  type Self
  def empty: Self
  extension (x: Self) def combine(y: Self): Self

  object MonoidLaws:
    def leftUnit(x: Self)(using Self is Eq): Boolean  = empty.combine(x) === x
    def rightUnit(x: Self)(using Self is Eq): Boolean = x.combine(empty) === x
    def associativity(x: Self, y: Self, z: Self)(using Self is Eq): Boolean =
      x.combine(y).combine(z) === x.combine(y.combine(z))
```

Without object evidence, a category cannot express "exactly one object", because `identity[A]` quantifies over all types. With evidence it can: take `Unit` as the single object, and give the evidence class an instance at `Unit` only.

```scala unit=Categories
trait One extends Type

object One:
  given UnitIsOne: Unit is One {}

def oneObject[M: Monoid]: Category { type Self[A, B] = M; type Obj = One } = new Category:
  type Self[A, B] = M
  type Obj        = One
  def identity[A: One]: M = M.empty
  def compose[A: One, B: One, C: One](g: M, f: M): M = g.combine(f)
```

So this category has exactly one object, and its arrows are the elements of the monoid. The category laws are the monoid laws. (Nothing stops someone from writing a second instance of `One` elsewhere; the single object is a convention of the companion, one more sign that evidence is not canonical.)

There is a second encoding, which avoids the evidence. Make every type an object, and give every hom the same type `M`:

```scala unit=Categories
def constant[M: Monoid]: Category { type Self[A, B] = M; type Obj = Type } = new Category:
  type Self[A, B] = M
  type Obj        = Type
  def identity[A: Type]: M = M.empty
  def compose[A: Type, B: Type, C: Type](g: M, f: M): M = g.combine(f)
```

`constant[M]` ignores the objects: its hom between any `A` and `B` is `M`. The category laws are again the monoid laws. But this category has every type as an object, and between any two objects A and B the hom is all of `M`. In particular, `Iso(M.empty, M.empty)` is an isomorphism between *any* two objects, because `empty` composed with `empty` is `empty`. **[Proved]** So in `constant[M]` all objects are isomorphic.

How do the two encodings relate? `oneObject` is literally the one-object category. `constant[M]` has many objects, but they are all isomorphic and every hom is a copy of the same monoid, so nothing expressible in the language of categories distinguishes it from the one-object category. The precise statement is that the two are *equivalent* categories, defined in chapter 13. `constant[M]` is usually more convenient, because it needs no evidence.

#### What categories can be defined?

| Objects | How | Example |
| --- | --- | --- |
| all types of kind \* | `Obj = Type` | `Total`, `OptionKleisli`, `Lenses` |
| the types with some evidence | `Obj` an evidence class | types with `Eq`; finite types (chapter 8) |
| exactly one type | an evidence class with one instance | a monoid as a one-object category |
| all types, all isomorphic | a hom that ignores its arguments | `constant[M]` |
| type constructors | a different class (chapter 10) | functors and natural transformations |
| values, such as numbers | not directly; chapter 8 | the preorder of integers, matrices |

The last row is the important limitation, and chapter 4 explains where it comes from.

### 3.9 An algorithm that only needs the laws

Composing an arrow f : A → A with itself n times can be done naively, or by repeated squaring:

```scala unit=Categories
def powerNaive(K: Category)[A: K.Obj](f: K.Self[A, A], n: Int): K.Self[A, A] =
  if n <= 0 then K.identity[A] else K.compose(f, powerNaive(K)(f, n - 1))

def power(K: Category)[A: K.Obj](f: K.Self[A, A], n: Int): K.Self[A, A] =
  if n <= 0 then K.identity[A]
  else
    val half    = power(K)(f, n / 2)
    val squared = K.compose(half, half)
    if n % 2 == 0 then squared else K.compose(f, squared)
```

The category is the first parameter, and the type parameter comes after it, so that the evidence `A: K.Obj` and the arrow types `K.Self[A, A]` can refer to it.

**Proposition 3.4.** In every lawful category, `power(K)(f, n)` = `powerNaive(K)(f, n)`. **[Proved]**

*Proof.* Write fⁿ for `powerNaive(K)(f, n)`. First, f^(m+n) = fᵐ ∘ fⁿ for m, n ≥ 0, by induction on m. For m = 0 this is left identity. For the step, f^(m+1+n) = f ∘ f^(m+n) = f ∘ (fᵐ ∘ fⁿ) = (f ∘ fᵐ) ∘ fⁿ = f^(m+1) ∘ fⁿ, using the induction hypothesis and associativity. Now show `power(K)(f, n)` = fⁿ by strong induction on n. For n ≤ 0 both sides are the identity. For n > 0, write k for n / 2, rounded down. By induction `half` = fᵏ, so `squared` = fᵏ ∘ fᵏ = f^(2k). If n is even, 2k = n. If n is odd, 2k = n − 1, and `compose(f, squared)` = f ∘ f^(n−1), which is fⁿ by definition. ∎

The proof used associativity and identity and nothing else, so the algorithm is correct in every lawful category. Whether it is *useful* depends on the category. For `Total` it saves nothing: the composite it builds still calls f n times when applied. For 2 × 2 matrices under multiplication it is the classic fast algorithm for Fibonacci numbers:

```scala unit=Categories
final case class Mat2(a: BigInt, b: BigInt, c: BigInt, d: BigInt) derives CanEqual

given Mat2IsMonoid: Mat2 is Monoid:
  def empty: Mat2 = Mat2(BigInt(1), BigInt(0), BigInt(0), BigInt(1))
  extension (x: Mat2)
    def combine(y: Mat2): Mat2 =
      Mat2(x.a * y.a + x.b * y.c, x.a * y.b + x.b * y.d, x.c * y.a + x.d * y.c, x.c * y.b + x.d * y.d)

val Matrices = constant[Mat2]

// The n-th power of [[1, 1], [1, 0]] is [[F(n+1), F(n)], [F(n), F(n-1)]].
def fib(n: Int): BigInt = power(Matrices)[Unit](Mat2(BigInt(1), BigInt(1), BigInt(1), BigInt(0)), n).b
```

This uses about log₂ n matrix multiplications instead of n. Note the division of labor. The theory guarantees that `power` computes the same arrow as `powerNaive`. It says nothing about speed; that comes from knowing how composition is implemented. Note also that `power` uses the arrow `half` twice. That innocent-looking duplication turns out to depend on a property of the enrichment, explained in section 4.2.

### 3.10 Checking the laws: tests and proofs

Propositions 3.1, 3.2 and 3.4 are proofs on paper. They are reliable to the extent the reader checks them, and they say nothing about whether the code on the page matches the code that runs. There are two ways to connect the laws to running code, and both use the Boolean laws of section 3.3.

**Property-based tests.** This is concession 1. A test generates arrows and sample points at random, constructs an `Observable` from the sample points, and checks that the law returns `true`. Here is a self-contained miniature of what the library's tests do with the ScalaCheck library:

```scala unit=Categories
/** Checks a law on `cases` generated cases. Drawing random numbers is an effect, so `law` has type `=>`. */
def holds(cases: Int)(law: scala.util.Random^ => Boolean): Boolean =
  val random = scala.util.Random(2026)
  (1 to cases).forall(_ => law(random))

/** A random affine function x ↦ a·x + b: a thin slice of all functions, but enough to refute a wrong law. */
def affine(random: scala.util.Random^): Int -> Int =
  val a = random.between(-5, 6)
  val b = random.between(-100, 101)
  x => a * x + b

/** Fresh sample points for every case. */
def points(random: scala.util.Random^): List[Int] = List.fill(6)(random.nextInt())

val associativityTested: Boolean = holds(1000) { random =>
  given (Int -> Int) is Observable = Observable.function(points(random))
  Total.CategoryLaws.associativity(affine(random), affine(random), affine(random))
}

val congruenceTested: Boolean = holds(1000) { random =>
  given (Int -> Int) is Observable = Observable.function(points(random))
  val (f, g) = (affine(random), affine(random))
  Total.CategoryLaws.congruence(f, x => f(x), g, x => g(x))
}
```

Three details are deliberate. The sample points are generated afresh for every case, so that no fixed set of points is ever trusted. The congruence check passes variants, `x => f(x)` for `f`, which are equal by construction, instead of sampling the premise. And the randomness lives in the generators, while the laws and the `Observable` remain pure. Capture checking enforces that division: it treats a random-number generator as a capability, written `Random^`, so a function that draws from one cannot have a pure type, and the law, which receives only the arrows and the `Observable`, cannot draw from it. The library's tests generate far more varied arrows: ScalaCheck builds random functions `A => B` from a generator for `B` and a way, called a `Cogen[A]`, to vary the generated result with the argument (from memory), and the generators for each category produce its interesting cases, such as functions that return `None` for `OptionKleisli`. The tests for `Lenses` use the observation `lenses(points)` of section 3.6.

Be clear about what a test establishes. A failing test is a genuine counterexample, provided the generated arrows are total, which these are. A passing test is evidence, not proof: it covers a few thousand points out of a usually infinite space, and the random functions are a thin slice of all functions. A law supported only this way is labeled **[Tested]**; the library records the status of every law it tests in a table that each test run regenerates (chapter 22).

**Proofs in Stainless.** Where code lies inside Stainless's subset, a law can be proved about the code itself. Because Stainless's dialect does not, as far as we know, accept the modularity syntax (section 2.3), the law is restated as a lemma over ordinary type parameters. It is the same Boolean law, specialized to the observation "apply at a". The following sketch is written in Stainless's dialect, so the document's checker does not compile it, and it has not been run through Stainless:

```scala sketch
import stainless.lang.*

object OptionKleisliLaws:
  def compose[A, B, C](g: B => Option[C], f: A => Option[B]): A => Option[C] =
    (a: A) => f(a).flatMap(g)

  def associativityAt[A, B, C, D](
      f: A => Option[B], g: B => Option[C], h: C => Option[D], a: A): Boolean = {
    compose(h, compose(g, f))(a) == compose(compose(h, g), f)(a)
  }.holds
```

Here `Option` is Stainless's own `stainless.lang.Option`. The lemma is stated for arbitrary functions and an arbitrary argument, so a successful verification proves the law at every argument, which by Definition 2.5 proves it outright. A law proved this way is labeled **[Checked: Stainless]**.

The examples of this chapter, with their current status:

| Category | Laws | Status |
| --- | --- | --- |
| `Total` | category laws | [Proved] (Proposition 2.9); [Tested] in the library |
| `OptionKleisli` | category laws | [Proved] (Proposition 3.1); [Tested] in the library; Stainless sketch exists |
| `Lenses` | category laws | [Proved] (Proposition 3.2) |
| `Lenses` | lens laws | not part of the type: chapter 6 |
| `opposite(K)` | category laws | [Proved] from those of `K`; [Tested] in the library for `Total` |
| `constant[Mat2]` | category laws, that is, the monoid laws | [Standard]: matrix multiplication is associative and unital |

### 3.11 The recipe

Defining a new category in Scala comes down to eight steps.

1. **Choose the arrows.** Write the type `Self[A, B]` of arrows from `A` to `B`.
2. **Choose the objects.** All types (`Obj = Type`), the types with some evidence, or a single type.
3. **Write identity and composition** as polymorphic functions, with composition in mathematical order.
4. **Decide when two arrows are equal.** For arrows that are functions, the default is the equality of chapter 2. Decide which observations you will use to test it: for function-valued arrows, application at sample points; for data, the data itself; for a record of functions such as `Lens`, applying each field.
5. **State the laws.** If you extend `Category`, they are already stated, as Boolean methods taking an `Observable`.
6. **Establish each law, and record how**: a proof on paper, a Stainless proof, or tests. Attach the status label.
7. **Check the contract** for identity, composition and the arrows you intend to use: capture checking for C1, Stainless or an assertion for C2, safe mode and review for C3.
8. **Write down what you wanted but could not express.** Typical entries are conditions on arrows, such as lawfulness of lenses; identifications between arrows, such as treating lists as sets; and objects that are not types, such as numbers. Chapter 4 explains why these gaps arise, and Part II shows how to handle each.

### 3.12 What the theory guarantees, and where it stops

Suppose identity and composition keep the contract, every arrow you use is total, and the laws hold. Then every theorem proved from the category laws holds for your category: Proposition 1.2, Proposition 3.4, and everything built on them in Parts II and III.

The guarantee stops in three places. It is a guarantee about the equality of chapter 2, so it says nothing about performance, as the two uses of `power` showed, and nothing about resources beyond the idealization in C2. A law that is only tested is a well-supported hypothesis, not a theorem. And if an arrow asserted to be total does not terminate, every conclusion that relied on the assertion is void, which is concession 3.

### 3.13 Set and Scala

In Set, you define a category by naming its hom-sets and its composition functions, and any sets and any functions are allowed: the hom between 3 and 5 can be anything you like, chosen separately for each pair of objects. In Scala, you name one type constructor and two polymorphic programs, and the objects come along with the type parameters. The hom must be a type, the structure must be programs, and the same programs must work at every object. You can restrict the objects with evidence, but you cannot pick a hom separately for each pair, and you cannot make numbers into objects directly. Chapter 4 gives these differences their names.

### References for chapter 3

**Consulted while writing this chapter**

- Scala 3 reference: "Better Support for Type Classes". https://scala-lang.org/api/docs/experimental/typeclasses.html
- Stainless repository README. https://github.com/epfl-lara/stainless

**Cited from memory, not consulted**

- ScalaCheck, in particular its generation of random functions via `Cogen`.
- The cats-laws library, whose law checking with Discipline and ScalaCheck is established practice in the Scala ecosystem.
- The lens laws, and the fact that lawful lenses are closed under composition.

---

## Chapter 4. What you actually defined: enriched categories

### 4.1 The idea: reading the definition again

Section 1.5 pointed out that the definition of a category quietly uses Set. The hom-set 𝒞(a, b) is a set. The identity on a is an element of 𝒞(a, a), which is the same thing as a function from a one-element set 1 into 𝒞(a, a). Composition is a function 𝒞(b, c) × 𝒞(a, b) → 𝒞(a, c). The laws are equations between functions.

So the definition takes four things from Set: a way to pair two objects (×), a unit object (1), arrows (functions), and equality of arrows. **Enrichment** means taking those four things from some other category 𝒱 instead. The rest of this chapter shows that a category written in Scala takes them from 𝒮, and traces what that implies.

### 4.2 Enrichment over a monoidal category

This section first gives the definition in the case this document needs, where the pairing is a product, and then the general case, for readers who want to see how far the idea extends.

**Definition 4.1 (enriched category, cartesian case).** Let 𝒱 be a category with a pairing operation × on its objects and a unit object 1 that behave like the cartesian product and a one-element set. A **𝒱-enriched category** 𝒞, or **𝒱-category**, consists of:

1. a collection of objects;
2. for every two objects a and b, an object 𝒞(a, b) of 𝒱, called the **hom-object**;
3. for every object a, an arrow j_a : 1 → 𝒞(a, a) of 𝒱, which picks out the identity;
4. for every three objects a, b and c, an arrow M : 𝒞(b, c) × 𝒞(a, b) → 𝒞(a, c) of 𝒱, which is composition;

such that the identity and associativity laws hold as equations between arrows of 𝒱.

With 𝒱 = Set this is exactly Definition 1.1, so an ordinary category is the same thing as a Set-enriched category (section 1.5).

**The general case.** Nothing in Definition 4.1 needs × to be a product. It only needs *some* way of combining two objects of 𝒱 into one, with a unit, behaving associatively. That structure has a name.

A **monoidal category** is a category 𝒱 together with:

- an operation ⊗, called the **tensor**, that combines two objects X and Y into an object X ⊗ Y and two arrows f : X → X′ and g : Y → Y′ into an arrow f ⊗ g : X ⊗ Y → X′ ⊗ Y′, preserving identities and composition;
- a **unit** object I;
- isomorphisms α : (X ⊗ Y) ⊗ Z ≅ X ⊗ (Y ⊗ Z), λ : I ⊗ X ≅ X and ρ : X ⊗ I ≅ X, which are compatible with all arrows of 𝒱 and satisfy two equations, called the pentagon and the triangle **[Standard: Mac Lane 1998, from memory]**.

Mac Lane's coherence theorem says that, given the pentagon and triangle, every diagram built from α, λ and ρ commutes, so the bracketing of a tensor of many objects never matters **[Standard: Mac Lane 1998, from memory]**. A **𝒱-category** for a monoidal 𝒱 is then defined exactly as in Definition 4.1 with ⊗ in place of × and I in place of 1, and with the laws adjusted by α, λ and ρ:

- associativity: M ∘ (M ⊗ id) = M ∘ (id ⊗ M) ∘ α, as arrows (𝒞(c, d) ⊗ 𝒞(b, c)) ⊗ 𝒞(a, b) → 𝒞(a, d);
- identity: M ∘ (j ⊗ id) = λ and M ∘ (id ⊗ j) = ρ.

This is the subject of Kelly's standard text **[Standard: Kelly 1982, from memory]**.

**Cartesian versus monoidal.** A monoidal category is **cartesian** when ⊗ is the categorical product and I is the terminal object; chapter 14 gives the precise definitions of both. The difference matters because a product comes with two kinds of arrow that a general tensor lacks: a **diagonal** Δ : X → X × X, which copies, and a **discard** X → 1, which deletes. In a cartesian 𝒱 you may use an element of a hom-object twice, or not at all. In a merely monoidal 𝒱 you may not, unless the structure provides a way.

The table shows a few monoidal categories and what their enriched categories are.

| 𝒱 | ⊗ | I | Cartesian? | 𝒱-categories are |
| --- | --- | --- | --- | --- |
| Set | × | one-element set | yes | locally small categories |
| truth values, with an arrow x → y when x implies y | and | true | yes | preorders (section 4.3) |
| [0, ∞], with an arrow x → y when x ≥ y | + | 0 | no: the product in this order is max, not + | generalized metric spaces (section 4.3) |
| the same | max | 0 | yes | generalized ultrametric spaces |
| abelian groups | tensor product | the integers | no | additive categories with several objects; a ring is such a category with one object |
| 𝒮 | tuples | `Unit` | yes (chapter 14) | the categories you write in Scala (section 4.4) |
| 𝒮 | `Either` | `Nothing` | no: it is the coproduct | categories whose composition receives *one* of two arrows; not useful |

Two points about 𝒮 are worth making here. First, the tuple types `((A, B), C)` and `(A, (B, C))` are different Scala types. The associator α is a genuine isomorphism between them, reassociating the tuple, and coherence is what lets us ignore the bracketing. Second, the enrichment being cartesian is not a technicality. The algorithm `power` of section 3.9 uses the arrow `half` twice, in `compose(half, half)`. In the language of enriched categories, that is the diagonal of the hom-object `K.Self[A, A]` followed by composition. Over a non-cartesian 𝒱 it could not be written. This is where separation checking (section 2.3) would lead: arrows that exclusively own mutable state cannot be copied, so a category of such arrows would be enriched over a monoidal, non-cartesian structure, and `power` would not apply to it. Whether Scala's separation checking gives such a structure in the precise sense is **[Open]**.

### 4.3 First examples: preorders and metric spaces

Let 𝒱 be the category 𝔹 whose two objects are the truth values false and true, with a single arrow x → y exactly when x implies y. The tensor is "and", and the unit is true.

A 𝔹-category assigns to every two objects a and b a truth value 𝒞(a, b), which you can read as "a ≤ b". The identity arrow j_a : true → 𝒞(a, a) exists only if 𝒞(a, a) is true: that is reflexivity. The composition arrow 𝒞(b, c) ∧ 𝒞(a, b) → 𝒞(a, c) exists only if "b ≤ c and a ≤ b" implies "a ≤ c": that is transitivity. The laws hold automatically, because 𝔹 has at most one arrow between any two objects. So a 𝔹-category is exactly a preorder **[Standard: Lawvere 1973, from memory]**.

Lawvere's paper has a second famous example. Take for 𝒱 the non-negative real numbers together with ∞, with an arrow x → y when x ≥ y, tensor given by addition and unit 0. An enriched category assigns a distance d(a, b) to every pair of objects. The identity arrow says 0 ≥ d(a, a), and composition says d(b, c) + d(a, b) ≥ d(a, c), which is the triangle inequality. So metric spaces, slightly generalized, are enriched categories. With max in place of + the triangle inequality becomes the ultrametric inequality.

The definition has the same shape in every case. What changes is what a hom can be and what composition is allowed to do.

### 4.4 Categories enriched in Scala

Now take 𝒱 = 𝒮, the category of total Scala programs from chapter 2, with tuples as the tensor and `Unit` as the unit. An 𝒮-category has:

- a hom-object 𝒞(A, B) that is a Scala type;
- an identity j_A, an arrow `Unit -> 𝒞(A, A)`. Since `Unit` has exactly one value, such a function is determined by what it returns, so this is the same as a value of type 𝒞(A, A);
- a composition M, an arrow `((𝒞(B, C), 𝒞(A, B))) -> 𝒞(A, C)`. This is the same as a two-argument composition method;
- laws that hold up to the equality of 𝒮.

That is precisely the `Category` class of chapter 3.

**Proposition 4.2.** Let `K` be a lawful `Category` whose `identity` and `compose` are total. Then the following is an 𝒮-category: the objects are the types with evidence `K.Obj`, 𝒞(A, B) is `K.Self[A, B]`, j_A is `_ => K.identity[A]`, and M is `(g, f) => K.compose(g, f)`. **[Proved]**

*Proof.* The data match Definition 4.1 item by item. The laws of an 𝒮-category are equations between arrows of 𝒮, that is, equalities ≐ between functions out of tuple types. By Definition 2.5 these hold exactly when they hold at every total argument, and at every argument they are the laws of `K`. ∎

So every category you write in Scala is an 𝒮-category. The hom between two objects is not a set but a type, and composition is not an arbitrary function but a program.

### 4.5 Two constraints: enrichment and uniformity

Proposition 4.2 says that every Scala-defined category is an 𝒮-category. The converse is false, and the reason is the second constraint of the central claim. This section takes its time with it.

#### What an 𝒮-category may do

Definition 4.1 asks for a hom-object for every *pair* of objects, an identity for every object, and a composition arrow for every *triple*. Nothing requires these choices to be related to each other. The objects can form any mathematical set: the integers, say. The hom between 3 and 5 can be one Scala type and the hom between 5 and 3 a completely different one. The composition at the triple (3, 5, 7) can be one program and at (7, 5, 3) another. An 𝒮-category is a family of types and programs, indexed by objects, and the family is assembled one object at a time in the meta-language.

#### What a Scala-defined category must do

A `Category` instance has none of that freedom. Its objects are not chosen; they are all the types of kind \*, or, with object evidence, the types that have some evidence. Its hom-objects are given by a single type constructor, `Self[A, B]`. Its identity is a single polymorphic value `identity[A]`, and its composition is a single polymorphic program `compose[A, B, C]`, which has to work at every triple of objects without knowing which triple it is at. Call a category of this kind **uniform**.

So the categories you can define in Scala form a proper subclass:

```
  Scala-definable categories     homs are types, structure is programs,
                                 objects are types, structure is uniform
            ⊊
  𝒮-enriched categories          homs are types, structure is programs
            │
            │ forget the enrichment (section 4.6)
            ▼
  ordinary categories            homs are sets, structure is functions
```

#### A worked example: ordering the natural numbers

The natural numbers with ≤ form an 𝒮-category. Its objects are the natural numbers. The hom 𝒞(m, n) is `Unit` when m ≤ n and `Nothing` otherwise. The identity on n picks out `()`, since 𝒞(n, n) is `Unit`. For composition at a triple (l, m, n) there are two cases. If l ≤ n, the target is `Unit`, and composition is `_ => ()`. If not, then l ≤ m and m ≤ n cannot both hold, so one component of the source tuple is `Nothing`; composition returns that component, which, being of type `Nothing`, has every type. The laws hold automatically: any two functions into `Unit` are equal, because under C2 they all return `()`, and any two functions out of an empty type are equal by property (E) of section 2.6. **[Proved]**

This is a perfectly good 𝒮-category. Can it be written as a Scala `Category`? Let us try three ways.

**Attempt 1: singleton types and match types.** The objects would have to be types, so the numbers become singleton types `0`, `1`, `2`, and so on, and the hom has to compute `Unit` or `Nothing` from two of them. Scala 3's match types can do that computation:

```scala unit=MatchTypes
import scala.compiletime.ops.int.<=

type Leq[A <: Int, B <: Int] = (A <= B) match
  case true  => Unit
  case false => Nothing

val threeFive: Leq[3, 5] = ()
```

The hom is fine for concrete objects: `Leq[3, 5]` reduces to `Unit`, so `()` has that type, and `Leq[5, 3]` reduces to `Nothing`. But composition cannot be written. For abstract `A`, `B` and `C`, the compiler cannot reduce `Leq[A, C]` to either case, so there is nothing of that type to return. The obvious attempt does not compile:

```scala unit=MatchTypes fails
def compose[A <: Int, B <: Int, C <: Int](g: Leq[B, C], f: Leq[A, B]): Leq[A, C] = ()
```

Only a cast would make it compile, and C3 forbids casts. Match types *compute* a type from other types, but a polymorphic program cannot *use* that computation when its type arguments are unknown. The definition also does not fit the `Category` class, because of the `<: Int` bounds.

**Attempt 2: a case class.** Represent an arrow by the two numbers it connects:

```scala
final case class LeqI(from: Int, to: Int) derives CanEqual // intended: from <= to

def compose(g: LeqI, f: LeqI): Option[LeqI] =
  if f.to == g.from then Some(LeqI(f.from, g.to)) else None
```

This compiles and works, but look at what it is. The objects have become *values*, the integers stored in the fields. There is a single hom type, `LeqI`, for all pairs of objects, and the arrows from 3 to 5 are not a type but a *subset* of `LeqI`: the values with `from == 3` and `to == 5`. The requirement `from <= to` is another subset condition, which nothing enforces. And composition has become partial, returning an `Option`, because the type checker no longer knows whether two arrows are composable. The case class moved the objects out of the types and into the values, and with them the bookkeeping of sources and targets, from compile time to run time. This is a category *as data*, studied in chapter 8, and it is not an 𝒮-category with the integers as objects.

**Attempt 3: proofs as data.** Keep the objects as types, but represent numbers by type-level constructors, and let an arrow be a *proof* that one number is at most another:

```scala
import tutorial.ch03.Categories.{Category, Type}

final class Z    // type-level zero; never instantiated
final class S[N] // type-level successor

enum Leq[A, B]:
  case Refl[A]() extends Leq[A, A]                      // A ≤ A
  case Step[A, B](prev: Leq[A, B]) extends Leq[A, S[B]] // A ≤ B implies A ≤ B + 1

def trans[A, B, C](g: Leq[B, C], f: Leq[A, B]): Leq[A, C] = g match
  case _: Leq.Refl[?] => f                        // here C is B
  case Leq.Step(prev) => Leq.Step(trans(prev, f)) // here C is S[C′] and prev: Leq[B, C′]

object Order extends Category:
  type Self[A, B] = Leq[A, B]
  type Obj        = Type
  def identity[A: Type]: Leq[A, A] = Leq.Refl()
  def compose[A: Type, B: Type, C: Type](g: Leq[B, C], f: Leq[A, B]): Leq[A, C] = trans(g, f)
```

From here on, code uses the `Category` class in the form section 3.8 gave it, with object evidence, and imports it from chapter 3.

This works. `Leq` is a **generalized algebraic data type** (GADT): each case fixes the type arguments of the enum in its own way, and pattern matching on a case tells the type checker what the type arguments must be. In the `Refl` case the compiler learns that `C` is `B`, so `f` already has the required type. In the `Step` case it learns that `C` is `S[C′]` for some `C′`, and the recursive call produces the rest. The recursion is structural on `g`, so it terminates.

**Proposition 4.3.** `Order` is a category in which there is at most one arrow between any two objects. Restricted to the types `Z`, `S[Z]`, `S[S[Z]]`, …, it is the order on the natural numbers. **[Proved, sketch]** A value of `Leq[A, B]` exists exactly when `B` is `A` with some number k of `S`s applied, and it then consists of exactly k `Step`s around a `Refl`, so it is unique. Since parallel arrows are equal, the category laws hold automatically.

The objects of `Order` are still all types: `String` is an object, with `String ≤ S[String]`. To restrict them to the type-level naturals, add evidence, as in section 3.8: an evidence class with instances for `Z` and for `S[N]` whenever `N` has one. Note also the cost: the mathematical arrow 3 → 5 carries no information, while its Scala representation is a proof object of size 2.

#### The lesson

Compare the 𝒮-category with attempt 3. The 𝒮-category defined composition by looking at the *objects*: at the triple (l, m, n), it asked whether l ≤ n. A uniform program cannot do that, because its objects are type arguments and C3 forbids inspecting type arguments. Attempt 3 defines composition by looking at the *arrows*: it matches on `g`, which is a value. The proof that the composite exists is carried by the arrows themselves.

> **Uniformity forbids branching on types. It allows branching on values: on arrows, and on evidence.** When a definition needs case analysis on objects, move the information into values that a program can inspect: into the arrows, as attempt 3 does, or into evidence about the objects, which turns information about an object into a value that programs may branch on (chapter 8).

Three further points follow.

- **Match types compute; GADTs prove.** A match type turns a type into a type, which helps state homs for concrete objects. A GADT carries a proof that programs can recurse on, which is what uniform composition needs.
- **Singleton types help name objects.** With singleton types, numbers and strings can appear as types, as in `Leq[3, 5]`. That makes more things expressible as objects, but it does not by itself make composition uniform.
- **These features are outside the model.** GADTs, match types and singleton types are not part of the formal core of appendix A. GADTs can be encoded in calculi like that core using an encoding of type equality **[Standard: Leibniz equality, from memory]**, so attempt 3 is plausibly within reach of the theory, but whether A1 and the parametricity results of chapter 9 survive GADT pattern matching unchanged is **[Open]**.

### 4.6 The underlying category, two ways

Most category theory is written about ordinary categories. When a mathematician reads "the category of Scala lenses", what are they looking at, and which of their theorems apply? The answer is an underlying category. There are two to compare: one is what ordinary category theory sees, and the other is what a program can work with.

**Definition 4.4 (underlying ordinary category).** The **underlying ordinary category** 𝒞₀ of an 𝒮-category 𝒞 has the same objects as 𝒞. Its hom-set 𝒞₀(a, b) is Val(𝒞(a, b)), the set of total values of the hom type, up to ≐. The identity on a is the value picked out by j_a, and the composite of two values is the result of applying M to the pair.

𝒞₀ is an ordinary category, that is, a Set-enriched one: its homs are sets and its composition is a function. Its laws follow from the laws of 𝒞 by applying Val. **[Proved]** For 𝒮 itself, regarded as an 𝒮-category with the function types as homs, the underlying category has the same arrows as 𝒮: the total values of type `A -> B` are the arrows A → B.

**Change of base.** Definition 4.4 is an instance of a general construction. Val is, up to isomorphism, the functor "arrows out of the unit": a total value of type X is the same thing as an arrow `Unit -> X` of 𝒮, which chapter 14 calls a *point* of X. And Val respects the monoidal structure: a value of a tuple type is a pair of values, and `Unit` has exactly one value. A functor between monoidal categories that respects their structure in this way, up to comparison arrows that turn a pair of images into the image of a pair, is called **lax monoidal**. Any lax monoidal functor F : 𝒱 → 𝒲 turns 𝒱-categories into 𝒲-categories, by applying F to every hom-object; this is **change of base** **[Standard: Eilenberg and Kelly 1966; Kelly 1982, from memory]**. For every monoidal category 𝒱, the functor 𝒱(I, −) of arrows out of the unit is lax monoidal into Set, and the underlying ordinary category of a 𝒱-category is its change of base along that functor **[Standard: Kelly 1982, from memory]**.

**The underlying 𝒮-category.** The same recipe has a second reading, which matters for code. Suppose 𝒱 is itself a category written in Scala, such as the preorders of section 4.3 written as code, and 𝒞 is a 𝒱-category. Then 𝒱(I, X) is not just a set but a Scala type: the type `V.Self[I, X]` of arrows from the unit to X. So 𝒱(I, −) can be read as a functor from 𝒱 into 𝒮.

**Definition 4.5 (underlying 𝒮-category).** For a 𝒱-category 𝒞, where 𝒱 is a monoidal category written in Scala, the **underlying 𝒮-category** is the change of base of 𝒞 along 𝒱(I, −) : 𝒱 → 𝒮. It has the objects of 𝒞, the hom types `V.Self[I, 𝒞(a, b)]`, and identities and composition given by programs.

For 𝒱 = 𝒮 it gives 𝒞 back, since `Unit -> X` and `X` are isomorphic types. **[Proved]** For any other 𝒱 it forgets the extra structure of the homs but keeps everything executable: its homs are types and its composition is code, so it is again a category in the sense of chapter 3. 𝒞₀ is what ordinary category theory sees; the underlying 𝒮-category is what a program can run. Chapter 20 meets a case where both matter: parsers carry a preorder on each hom that compares their error messages, which makes them a category enriched over preorders, and forgetting the preorders gives back the category of parsers that the library runs.

So the views have the same objects and, in the end, the same arrows. What does enrichment change? It changes **which maps between categories exist**.

**Definition 4.6 (𝒮-functor).** An **𝒮-functor** F from an 𝒮-category 𝒞 to an 𝒮-category 𝒟 assigns to every object a of 𝒞 an object F(a) of 𝒟, and to every two objects a and b an *arrow of 𝒮*

F_{a,b} : 𝒞(a, b) → 𝒟(F(a), F(b)),

that is, a Scala function from one hom type to the other, such that identities and composites are preserved up to the equality of 𝒮.

An ordinary functor between the underlying categories 𝒞₀ and 𝒟₀ is the same thing with *any function between sets* Val(𝒞(a, b)) → Val(𝒟(F(a), F(b))) in place of a Scala function. Every 𝒮-functor gives an ordinary functor, by applying Val. **[Proved]** The converse fails.

**Example.** Consider two monoids, regarded as one-object 𝒮-categories with the encoding of section 3.8:

- P: the type `BigInt -> Boolean`, combined pointwise with `&&`, with unit `_ => true`;
- B: the type `Boolean`, combined with `&&`, with unit `true`.

Define h(p) to be `true` exactly when p(n) is `true` for every n. Then h is a monoid homomorphism, that is, a functor between one-object categories (section 1.4): a pointwise conjunction is true everywhere exactly when both parts are, and the constant `true` predicate is true everywhere. But no program computes h **[Standard: reduction to the halting problem]**. For any program e, the predicate "e has not halted after n steps" is a total, computable value of P, and h sends it to `true` exactly when e never halts.

So h is a functor between the underlying ordinary categories P₀ and B₀, but there is no 𝒮-functor from P to B with the same action, because an 𝒮-functor acts on arrows by a Scala function, and no Scala function computes h.

**Consequences.** When you apply a theorem of ordinary category theory to a Scala category, you are applying it to the underlying ordinary category. Theorems that assert *equations* transfer: Val is faithful (Proposition 2.10), so an equation that holds in the underlying category holds in 𝒮. Theorems that assert the *existence* of a functor, an arrow or an inverse do not, in general: what they produce may exist in the underlying category without being a program. This is the same lesson as in section 2.10, now one level up.

### 4.7 What follows

The two constraints are not abstract. Each produces a concrete wall that you hit when defining categories in Scala, and each wall has a characteristic workaround. Part II takes them one chapter at a time. In the table, **E** marks consequences of enrichment and **U** consequences of uniformity.

| Consequence | Constraint | Running example | Chapter |
| --- | --- | --- | --- |
| Arrows are programs: equality is observational and must be tested or proved; homs are countable; maps between categories must be programs | E | the homomorphism h of section 4.6 | 5 |
| Composition must be computable | E | Rel: composing relations needs a search over the middle object | 5, 8 |
| No subset types: arrows cannot be restricted by an equation | E | lawful lenses; monoid homomorphisms | 6 |
| No quotient types: arrows cannot be identified beyond the equality of 𝒮 | E | finite sets represented as lists; the finite powerset | 7 |
| Objects must be types | U | the order on numbers (section 4.5); matrices indexed by dimension | 8 |
| Some laws hold for free | U | naturality of polymorphic functions | 9 |
| One kind of object per class | U | categories of type constructors | 10 |

### 4.8 Rel and Mat: a closer look

Two examples from chapter 1 show the constraints at work particularly clearly, and they show that a single mathematical category can split into several different Scala categories, each capturing part of it. Part II gives the code; this section maps the options.

#### Rel

What is a relation between `A` and `B` in Scala? There are several candidates, and each leads to a different category.

- **Decidable predicates**, `(A, B) => Boolean`. Equality of predicates is extensional, which matches equality of relations as sets of pairs. But composition asks whether *some* b relates a to c, and for an infinite middle type that search is not a program (chapter 5). Composition is not an arrow of 𝒮, so this is not an 𝒮-category. Enrichment fails.
- **Decidable predicates between finite types.** Restrict the objects to types with evidence that lists all their values. Then the search for b is a finite loop, composition is computable, and the result is a genuine Scala category on the finite types (chapter 8). The price is the restriction of objects.
- **Multi-valued functions**, `A => List[B]`. Composition is computable: apply, then flat-map. This is the Kleisli category of `List`. But its arrows carry an order and multiplicities, which relations do not have: the lists `List(1, 2)` and `List(2, 1, 1)` are different arrows but the same relation. Getting Rel back requires identifying such lists, a quotient (chapter 7).
- **Existential witnesses.** A relation can be represented by a hidden type `W` of witnesses with two functions `W => A` and `W => B`, a *span*, packaged with `W` as an abstract type member. Scala 3 has no separate syntax for existential types, but an abstract type member plays exactly that role. Composition then needs no search: a witness of the composite is a pair of witnesses whose middle elements agree. That agreement condition is again a subset, so the composite's legs become partial, or the check is postponed. And because `W` is hidden, the only way to *observe* a relation is through the interface packaged with it; to ask whether a particular pair is related, the interface must enumerate the witnesses. Existential types move the search out of composition and into observation.
- **Enumerations**, `LazyList[(A, B)]`, describe relations whose pairs can be listed. Composition is computable by interleaving the two enumerations, but the representation is infinite data, outside the model of this document.

No candidate gives all of Rel. Each keeps a different part of it: finite middle objects, computable composition, or decidable membership.

#### Mat

The objects of Mat are numbers, and numbers are not types. Again there are several ways to proceed.

- **Singleton types with evidence.** Let the objects be singleton types such as `3`, and let the hom be an opaque matrix type indexed by them, `Matrix[N, M]`, whose representation is a vector of rows. Identity needs the actual value of `N` at run time, which is available from Scala's `ValueOf[N]`: a category whose object evidence carries the dimension. The dimensions in the types make composition type-check only for matching sizes, but that the representation actually has those dimensions is a subset condition, maintained by a smart constructor (chapter 6).
- **Type-level naturals and indexed vectors.** Use `Z` and `S[N]` as in section 4.5 and a GADT of vectors indexed by their length. A matrix is then a vector of vectors, and its dimensions are guaranteed by its type, with no subset condition at all. Identity needs a value-level natural, as evidence. The representation is a linked structure, which is slow.
- **Path-dependent types for dimensions known only at run time.** If `val n: Int` is read from input, then `n.type` is a type, so an object can be created at run time. This is a genuine form of dependent typing, and it lies outside the model **[Open]**.

Singleton types and path-dependent types help *name* dimensions as types; GADTs help *enforce* them; and evidence supplies the run-time values that uniform programs need. Chapter 8 develops each option.

### 4.9 Set and Scala

An ordinary category is enriched in Set: its homs are sets, its identities are elements, its composition is a function, and each can be chosen freely and separately for every pair or triple of objects. A Scala category is enriched in 𝒮: its homs are types, its identities are values and its composition is a program, with equality meaning the equality ≐ of 𝒮. And it is uniform: the hom is one type constructor, the structure is one pair of polymorphic programs, and the objects are types, possibly restricted by evidence. Both views share a common shadow, the underlying ordinary category, which has the same objects and arrows. What distinguishes them is which maps between categories exist, and, as Part II shows, which constructions on homs are available.

| | Ordinary (Set-enriched) | 𝒮-enriched | Scala-definable |
| --- | --- | --- | --- |
| Objects | any collection | any set | the types of one kind, possibly filtered by evidence |
| Hom between two objects | a set, chosen per pair | a type, chosen per pair | `H[A, B]` for one type constructor `H` |
| Identity | an element | a value of the hom type | one polymorphic value `identity[A]` |
| Composition | any function, chosen per triple | a program, chosen per triple | one polymorphic program `compose` |
| Equality of arrows | equality | the equality ≐ of 𝒮 | ≐, tested or proved |
| Size of a hom | any size | countable | countable |
| Arrows restricted by an equation | a subset, always available | not available | not available |
| Arrows identified by an equivalence | a quotient, always available | not available | not available |
| Maps between categories | functors: any functions on homs | 𝒮-functors: programs on homs | programs, uniform in the objects |

### References for chapter 4

**Cited from memory, not consulted**

- G. M. Kelly, *Basic Concepts of Enriched Category Theory*, Cambridge University Press, 1982: enriched categories, the underlying category via 𝒱(I, −), change of base along lax monoidal functors.
- Samuel Eilenberg and G. M. Kelly, "Closed categories", *Proceedings of the Conference on Categorical Algebra*, La Jolla 1965, Springer, 1966.
- F. William Lawvere, "Metric spaces, generalized logic, and closed categories", *Rendiconti del Seminario Matematico e Fisico di Milano* 43, 1973.
- Saunders Mac Lane, *Categories for the Working Mathematician*, 2nd ed., Springer, 1998, for monoidal categories and the coherence theorem.
- The encoding of type equality as Leibniz equality in polymorphic calculi.

---

## Summary of Part I

A category is objects, arrows, identities and an associative composition, and functors are the maps between categories (chapter 1). Scala programs that are pure and respect representations form a category 𝒫, with observational equality; the programs among them that always terminate form a category 𝒮, with an equality defined type by type, which makes extensionality a definition and testing meaningful. Without totality, something basic has to give, whichever evaluation strategy is used; with it, the functor Val maps 𝒮 faithfully into Set but reaches only its computable part (chapter 2). To define your own category in Scala you choose a hom type constructor, the objects, as a type class of evidence, and two polymorphic programs, and you establish the laws, which are stated inside the class as Boolean functions checked through an `Observable`, by proof, by Stainless, or by tests (chapter 3). What you get is an 𝒮-enriched category, and moreover a uniform one: its homs are types, its structure is programs, its objects are types, and its structure is the same program at every object. Uniformity forbids case analysis on types but allows it on values, arrows and evidence alike, and enrichment changes which maps between categories exist (chapter 4).

Part II takes the consequences one at a time.

---

# Part II. Consequences

Part I established that a category written in Scala is enriched in 𝒮 and uniform. This part takes the consequences one at a time. Chapters 5 to 7 follow from enrichment: arrows are programs, there are no subset types, and there are no quotient types. Chapters 8 to 10 follow from uniformity: objects must be types, polymorphic structure obeys free theorems, and each kind of object needs its own class. Every chapter ends with the workarounds that practice has found and what each one actually buys.

## Chapter 5. Arrows are programs

### 5.1 The idea

In an ordinary category, a hom-set is just a set. It has no internal structure, nothing about it needs to be computable, and its elements can be compared, counted and chosen at will. In a Scala category, a hom is a type, and its values are programs, or data containing programs. This chapter collects what follows. Some of it is restriction: equality of arrows cannot be decided, composition must be computable, and maps between categories must be programs. Some of it is power: arrows are values that programs can build, store and pass around.

### 5.2 Equality of arrows cannot be decided, except when arrows are data

Proposition 2.1 showed that equality of functions `BigInt -> Boolean` is undecidable. The same argument applies to the arrows of any Scala category whose arrows contain functions with infinite argument types: `Total`, `OptionKleisli`, `Lenses`, and most Kleisli categories. Concretely, in such a category you cannot write:

- `isIdentity(f)`, a test whether an arrow equals the identity;
- a cache keyed by arrows, since keys must be compared;
- a run-time check that a diagram commutes;
- duplicate elimination in a collection of arrows.

Algorithms from category theory that compare arrows, such as checking that a diagram commutes or rewriting words in a presented category to a normal form, are therefore available only when the arrows are data. Arrows are data in a category such as `constant[List[Char]]`, whose arrows are strings, or the typed path category of section 8.4, whose arrows are sequences of steps. There, `===` exists and these algorithms work.

**Sampled equality is sound for refutation, but it is not a congruence.** For a fixed finite set of sample arguments, "agrees on every sample" is a genuine equivalence relation on arrows: reflexive, symmetric and transitive. It is coarser than equality: arrows that are equal agree on every sample, but arrows that agree on every sample may still differ. **[Proved]** So sampling can refute equality, never confirm it. That is the precise status of a passing property test.

Sampled agreement has a second defect, and it is easy to miss: composition does not respect it. Take the single sample point 0:

```scala
import tutorial.ch03.Categories.*
import Eq.given
import Total.>>>

val atZero = Observable.function[Int, Int](List(0))

val f: Int -> Int  = x => x + 1
val f2: Int -> Int = x => if x == 0 then 1 else 7
val g: Int -> Int  = x => x
val g2: Int -> Int = x => if x == 0 then 0 else 99

val partsAgree: Boolean      = atZero.agree(f, f2) && atZero.agree(g, g2) // true
val compositesAgree: Boolean = atZero.agree(f >>> g, f2 >>> g2)            // false: 1 and 99
```

f and f′ agree at 0, and so do g and g′, but g ∘ f sends 0 to 1 while g′ ∘ f′ sends 0 to 99: the composite passes through the point 1, which is not a sample. **[Proved]** So an `Observable` is an equivalence relation on arrows that is not a congruence, and conclusions drawn from it do not compose. Two practices in this document follow. A test chooses its sample points for the very arrows it compares, afresh for every law; and a law whose premise is an equation, such as the congruence law of section 3.3, is checked with variants that are equal by construction, never with arrows that merely agree on samples.

### 5.3 Arrows are values

The flip side of homs being types is that arrows are first-class values. Every hom-object `H[A, B]` is itself an object of 𝒮, so the arrows of any Scala category can be put in lists, passed to functions, returned from functions and built by combinators. That is what makes Kleisli arrows, lenses and parsers practical: a parser combinator library is a collection of programs that take arrows and return arrows.

This also gives a clean example of the difference between the meta-language and the category language. Consider predicates on `BigInt`.

- **In the meta-language**, Val(`BigInt -> Boolean`) is a countable set (Proposition 2.13), and so is Val(`BigInt`). Two countable infinite sets are in bijection, so *there is a function* from Val(`BigInt`) onto Val(`BigInt -> Boolean`).
- **In the category language**, there is no arrow f : `BigInt` → (`BigInt -> Boolean`) that reaches every predicate. **[Proved]** Given any `f`, the predicate `d = (n: BigInt) => !f(n)(n)` is total, and it differs from every `f(n)` at the argument n.

Both statements are true. They do not contradict each other, because the bijection in the first statement is a function between sets, not a program. Mixing the two languages produces a false statement: "the predicates on `BigInt` are countable, so some program enumerates them all". Lawvere showed that this diagonal argument works in any category with products and function types **[Standard: Lawvere 1969, from memory]**: if some arrow A → (A ⇒ B) reaches every point of A ⇒ B, then every arrow B → B has a fixed point. Since negation on `Boolean` has no fixed point, no such arrow exists in 𝒮.

### 5.4 Composition must be computable

Composition of an 𝒮-category is an arrow of 𝒮, so it must be a program. This rules out categories whose composition is well defined in Set but not computable. Rel with decidable predicates is the standard example.

**Proposition 5.1.** There is no program that computes the composite of two relations given as predicates, already when the middle type is `BigInt`. **[Proved, by reduction to the halting problem]**

*Proof.* Suppose `relCompose` took predicates `r: (Unit, BigInt) => Boolean` and `s: (BigInt, Unit) => Boolean` to their composite `(Unit, Unit) => Boolean`, which is `true` exactly when some n satisfies both. Take `s` to be always `true`, and for a program e let `r((), n)` be "e halts within n steps". The composite is `true` exactly when e halts, so `relCompose` would decide the halting problem. ∎

The failure is not about uniformity. Even for the single middle object `BigInt`, chosen in advance, composition is not a program. Rel with decidable predicates is a perfectly good ordinary category, but it is not an 𝒮-category. Section 4.8 listed the repairs: restrict the middle objects to finite types (chapter 8), or change what an arrow is (chapter 7).

### 5.5 Maps between categories must be programs

Section 4.6 showed that an 𝒮-functor acts on arrows by a Scala function, and that some ordinary functors between underlying categories, such as the "true everywhere" homomorphism, have no such action. Uniformity adds a further requirement on Scala-definable functors: their *object map* must also be expressible. Since objects are types, a functor's object map is a type constructor, and a type constructor cannot inspect its argument except through match types. Chapter 12 writes functors as Scala classes; here are the two consequences to keep in mind.

1. **The arrow map is a program.** Every theorem that constructs a functor by an existence argument may produce something without a Scala counterpart.
2. **The object map is a type constructor.** A functor whose action on objects depends on what the object is, sending `Int` one way and `String` another, is not expressible uniformly, for the same reason that composition in section 4.5 could not branch on objects.

### 5.6 Set and Scala

| | Set | Scala category |
| --- | --- | --- |
| Equality of arrows | equality of elements of a set | undecidable for function-valued arrows; decidable when arrows are data |
| Arrows as values | the hom-set is a set, an object of Set | the hom-object is a type, an object of 𝒮 |
| Counting arrows | the meta-language counts freely | countable externally; internal diagonal arguments still hold |
| Composition | any function | a program |
| Functors | any object map, any arrow map | a type constructor and a program |

### References for chapter 5

**Cited from memory, not consulted**

- F. William Lawvere, "Diagonal arguments and cartesian closed categories", in *Category Theory, Homology Theory and their Applications II*, Lecture Notes in Mathematics 92, Springer, 1969.
- The undecidability of the halting problem (Turing).

---

## Chapter 6. No subset types

### 6.1 The idea

In Set, every condition cuts out a subset: given a set A and a property φ, there is the set { a ∈ A | φ(a) }. When the condition is an equation f(a) = g(a) between two functions f, g : A → B, category theory describes the subset by its arrows.

**Definition 6.1 (equalizer).** An **equalizer** of two arrows f, g : A → B is an object E with an arrow e : E → A such that f ∘ e = g ∘ e, and such that every arrow k : Z → A with f ∘ k = g ∘ k factors as k = e ∘ u for exactly one arrow u : Z → E.

In Set, E is the subset { a | f(a) = g(a) } and e is its inclusion. The definition says that E is the best possible place for arrows that satisfy the equation to land: every such arrow passes through E, in exactly one way.

### 6.2 Where you meet it

Many categories that programmers want are carved out of bigger ones by equations.

- **Lawful lenses.** The get-set law cuts the lawful lenses out of `Lens[S, A]`: it is the equalizer of the two maps from `Lens[S, A]` to `(S, A) => A` that send a lens l to `(s, a) => l.get(l.set(s, a))` and to `(s, a) => a`. The other two laws add two more equations.
- **Monoid homomorphisms.** The homomorphisms from one monoid to another are the functions h with h(e) = e and h(x · y) = h(x) · h(y), a subset of a function type.
- **Categories of algebraic structures.** Monoids, groups, F-algebras: in each, the arrows are the functions that preserve the structure, so every hom is a subset of a function type.
- **Everyday invariants.** Sorted lists, positive numbers, validated input, balanced trees.

### 6.3 What 𝒮 lacks, precisely

Two separate facts are easy to confuse.

**Fact 1: there is no subset type former.** **[Proved, from the shape of the type language]** In the model, types are built from other types; they never mention values. So there is no type `{ x: A | p(x) }` built from a predicate p, and no type "lenses satisfying the laws". Scala's singleton and path-dependent types are a partial exception, because they let some types mention values; they lie outside the model.

**Fact 2: particular subsets may still be represented by other types.** The even numbers are not a type, but `BigInt` with the arrow `n => 2 * n` has the defining property of the equalizer of "n is even" and "true" **[Proved]**. Non-empty lists are not a subset type, but `(A, List[A])` represents them. Section 6.8 gives a less obvious example. Whether *every* equalizer of arrows in 𝒮 exists in 𝒮, found by some clever choice of representing type for each pair of arrows, is a subtle question. For equations between function-valued results, such as the lens laws, we know of no construction **[Open]**.

The consequence for categories is this. The lawful lenses, the monoids with their homomorphisms, and the algebras of a functor all form ordinary categories, the underlying categories of section 4.6 with subsets as homs. They are not 𝒮-categories unless a type representing each hom can be found.

### 6.4 Workaround 1: accept the bigger category

`Lens` as defined in chapter 3, with all get/set pairs, is an honest Scala category. Every theorem about categories applies to it. Theorems that need the lens laws apply to the lawful lenses inside it, with the laws as explicit hypotheses about each arrow involved. Many libraries take this route, sometimes without saying so: the type is bigger than the intended set, and lawfulness is a convention.

This is the right choice when the laws are only needed occasionally, or when the bigger category is genuinely useful in its own right. Unlawful lenses are sometimes exactly what is wanted, for instance a "lens" that normalizes the value it writes.

### 6.5 Workaround 2: abstraction

An opaque type can stand in for a subset:

```scala
import tutorial.ch03.Snippets.{Lens, Lenses}
import tutorial.ch03.Categories.{Category, Type}

object lawful:
  opaque type LawfulLens[S, A] = Lens[S, A]

  object LawfulLens:
    // Every exported constructor produces a lawful lens.
    def first[A, B]: LawfulLens[(A, B), A]  = Lens(_._1, (p, a) => (a, p._2))
    def second[A, B]: LawfulLens[(A, B), B] = Lens(_._2, (p, b) => (p._1, b))
    def identity[A]: LawfulLens[A, A]       = Lens(a => a, (_, a) => a)

    extension [S, A](l: LawfulLens[S, A])
      def read(s: S): A        = l.get(s)
      def write(s: S, a: A): S = l.set(s, a)

  object LawfulLenses extends Category:
    type Self[A, B] = LawfulLens[A, B]
    type Obj        = Type
    def identity[A: Type]: LawfulLens[A, A] = LawfulLens.identity
    def compose[A: Type, B: Type, C: Type](g: LawfulLens[B, C], f: LawfulLens[A, B]): LawfulLens[A, C] =
      Lenses.compose(g, f)
```

Inside the object `lawful`, `LawfulLens` is just `Lens`, and the category reuses the composition of `Lenses`. Outside, it is an abstract type, and clients can only obtain values through the exported constructors and composition, and read and write through `read` and `write`. If every exported operation produces lawful lenses, every value a client can ever hold is lawful.

Why does this make the opaque type behave like the subset? Because of representation independence (C3). A client cannot cast an arbitrary `Lens` into a `LawfulLens`, and cannot observe a `LawfulLens` except through the exported operations. Reynolds's abstraction theorem makes this precise for polymorphic languages: clients of an abstract type cannot distinguish two implementations related by a relation that the operations preserve **[Standard: Reynolds 1983, from memory; assumed for Scala as part of A2, chapter 9]**. Here the relation says "is a lawful lens", and the theorem says clients see exactly the lawful lenses.

In the model, an opaque type is an existential type: an abstract type packaged with its operations. So `LawfulLens[S, A]` is an object of 𝒮, a type, whose values are representations, and up to what clients can observe it *is* the subset. **Abstraction is Scala's substitute for subset types.**

Three cautions. The opaque type is not literally the subset: inside the defining scope, an unlawful lens can be given the opaque type by mistake. The proof obligation is real: each exported constructor must produce lawful lenses, and composition must preserve lawfulness (section 3.6), established by proof, by Stainless or by tests. And the guarantee depends on C3: a cast outside the module breaks it, which is one more reason to compile with safe mode.

### 6.6 Workaround 3: put the invariant into the type

When an invariant is structural, a cleverer type can express it exactly, with no subset condition left over.

- Non-empty lists: `(A, List[A])`, or a case class with a head and a tail.
- Vectors of known length: the GADT `Vec[N, A]` of section 4.8, indexed by a type-level natural.
- Typed state machines: a GADT of transitions indexed by source and target states (section 8.4), so that only legal sequences of transitions are expressible.

This works when the invariant is about shape. It does not work for invariants that are equations between functions, such as the lens laws.

### 6.7 Workaround 4: verified invariants with Stainless

Stainless supports invariants on the constructor parameters of algebraic data types, preconditions with `require`, and postconditions with `ensuring` [EuroProofNet wiki on Stainless, checked]. For example, in Stainless's dialect, which this document's checker does not compile:

```scala sketch
import stainless.lang.*

final case class Positive(n: BigInt):
  require(n > 0)

def double(p: Positive): Positive = Positive(p.n * 2)  // Stainless proves the invariant holds
```

Stainless proves that every construction of a `Positive` satisfies the invariant. In the verified world this is a genuine subset type. In plain Scala, the `require` is checked at run time and throws on failure, which would break C2; the point of the verification is to show that it never fails. Invariants of this kind are limited to what Stainless can state and prove, and equations between functions are hard for it.

### 6.8 The category of monoids, honestly

Monoids show all four workarounds at once. The objects are types with a `Monoid` instance, which is object evidence in the sense of section 3.8. The arrows should be homomorphisms.

- *The bigger category* takes all functions between carriers. It is a Scala category, but its arrows are mostly not homomorphisms.
- *Abstraction* takes an opaque type of homomorphisms with constructors that produce only homomorphisms: identities, composites, and the homomorphisms described next.
- *A representing type* exists for one important case. For the **free monoid** `List[A]`, the homomorphisms from `List[A]` to a monoid `N` correspond exactly to the functions `A => N`. Given `f: A => N`, the homomorphism is `foldMap(f)`, which sends a list to the combination of the images of its elements:

  ```scala
  import tutorial.ch03.Categories.Monoid

  def foldMap[A, N: Monoid](f: A -> N)(xs: List[A]): N =
    xs.foldLeft(N.empty)((acc, a) => acc.combine(f(a)))
  ```

  Every `foldMap(f)` is a homomorphism, and every homomorphism h from `List[A]` equals `foldMap(a => h(List(a)))` **[Proved in chapter 15]**. So the subset "homomorphisms from `List[A]` to `N`" is represented, without any subset condition, by the type `A -> N`. This is an instance of Fact 2 in section 6.3, and it is no accident: it is the free monoid adjunction of chapter 15.

### 6.9 Set and Scala

In Set, a subset is always available, so any category of structured sets and structure-preserving maps is immediately a category. In Scala, the type of structure-preserving maps does not exist as such. You either accept a bigger type, hide the representation behind an abstraction whose operations preserve the structure, design a type in which only valid values are expressible, or verify the invariant with Stainless. Each workaround keeps a different part of what the subset would have given.

| Workaround | What you get | Obligation | Limits |
| --- | --- | --- | --- |
| Bigger category | an honest Scala category | laws as hypotheses where needed | the intended arrows are not a type |
| Abstraction (opaque type) | a type that behaves like the subset for clients | exported operations preserve the invariant; C3 | not literally the subset inside the module |
| Invariant in the type | an exact representation | design a suitable type | only structural invariants |
| Stainless invariants | a verified subset in the Stainless world | proofs | what Stainless can prove |

### References for chapter 6

**Consulted while writing this chapter**

- EuroProofNet wiki, "Stainless". https://github.com/EuroProofNet/ProgramVerification/wiki/Stainless

**Cited from memory, not consulted**

- John C. Reynolds, "Types, abstraction and parametric polymorphism", *Information Processing 83*, North-Holland, 1983.
- The equational presentation of lens laws, and the free monoid.

---

## Chapter 7. No quotient types

### 7.1 The idea

In Set, every equivalence relation gives a quotient: the set A/~ of equivalence classes. The rational numbers are pairs of integers modulo the relation (a, b) ~ (c, d) when ad = bc. A finite set can be represented by a list, modulo reordering and repetition. Category theory describes quotients through **coequalizers**, the mirror image of Definition 6.1: a coequalizer of f, g : A → B is an arrow q : B → Q with q ∘ f = q ∘ g through which every other such arrow factors uniquely. In Set, Q is B modulo the equivalence relation generated by f(a) ~ g(a).

### 7.2 Where you meet it

- **Sets as lists.** `List(1, 2)` and `List(2, 1, 1)` represent the same finite set.
- **Relations as multi-valued functions.** The Kleisli category of `List` (section 4.8) has arrows that differ only by order and multiplicity of results, yet represent the same relation.
- **Free structures with relations.** Words in a free monoid modulo commutativity give multisets; paths in a graph modulo some equations give a category presented by generators and relations.
- **Numbers.** Rationals as pairs of integers, integers modulo n.

### 7.3 What 𝒮 lacks, precisely

**There is no quotient type former.** **[Proved, from the shape of the type language]** Nothing in the model takes a type and an equivalence relation and produces a type whose values are the classes.

**Equality is fixed by the language.** **[Proved, given A1]** Two total values of a type are equal in 𝒮 exactly when no program can tell them apart (Proposition 2.6 and assumption A1). `List(1, 2)` and `List(2, 1)` are distinguished by `head`, so they are different values of `List[Int]`, whatever we intend them to mean. We cannot declare two values equal; we can only arrange that no program observes their difference.

A cautionary example from the standard library makes the second point concrete. Scala's immutable `Set` has an `equals` that compares elements, so `Set(1, 2) == Set(2, 1)` is `true`. But the small sets of up to four elements remember the order of insertion, so `Set(1, 2).toList` and `Set(2, 1).toList` are different lists **[Standard: behavior of the standard library's small sets, from memory]**. Some programs can therefore tell two `==`-equal sets apart. In the terms of section 2.3, `Set`'s `equals` is a custom equality coarser than observational equality, and `Set` is not a data type in our sense. It is also not a quotient type, because its own operations observe the representation.

### 7.4 Workaround 1: setoids

Carry the equivalence relation explicitly. A **setoid** is a type together with an equivalence relation on it. For a type whose values are data, the equivalence can be an `Eq` instance that is coarser than structural equality:

```scala
import tutorial.ch03.Categories.*
import Eq.given

/** Finite sets represented as lists; two lists are equivalent when they have the same elements. */
def sameElements[A: Eq]: List[A] is Eq = new Eq:
  type Self = List[A]
  def equal(xs: List[A], ys: List[A]): Boolean =
    xs.forall(x => ys.exists(_ === x)) && ys.forall(y => xs.exists(_ === y))
```

A **setoid-enriched category** has setoids as hom-objects. Composition must then respect the equivalence: if f ~ f′ and g ~ g′, then g ∘ f ~ g′ ∘ f′. This document, and the library, state this directly rather than building a separate theory of enriched categories: a setoid-enriched category is a `Category` whose homs carry a semantic `Eq`, together with the congruence law of section 3.3. This is the implication-shaped law that section 3.3 noted cannot be checked by sampling its premise. As a Boolean law it reads "for these particular equivalent inputs, the outputs are equivalent", and a test must generate equivalent pairs deliberately, as variants: for instance by shuffling and duplicating a list.

For the Kleisli category of `List`, with arrows compared pointwise by `sameElements`, composition respects the equivalence: if `f(a)` and `f′(a)` have the same elements, so do their flat-maps by `g`. **[Proved]** The resulting category is relations with finite images, a large part of Rel.

The weakness of setoids is that *every* function in the program must respect the equivalence, not just the category's composition. A program that takes the `head` of a list-represented set breaks the abstraction silently. Respecting the equivalence is a convention unless it is enforced by abstraction.

Setoids are the standard way to add quotients to type theories that lack them **[Standard, from memory]**, and the category of setoids can be seen as 𝒮 with quotients added freely.

**Two equalities on one type.** `List[A]` now has two `Eq` instances: the elementwise `ListIsEq` of chapter 3 and `sameElements`. Which one a given `===` uses depends on which instance the compiler finds at that point, and nothing stops two parts of a program from finding different ones. A collection that deduplicates its elements with one equality and is queried with the other gives answers that contradict each other. Evidence found by search is called **coherent** when every search for the same type finds the same instance, or at least instances that behave the same. Scala does not enforce coherence; Haskell, for instance, insists on at most one instance per type in a whole program **[Standard, from memory]**. Subtyping between evidence classes makes the question sharper: since `Eq` extends `Type`, a search for `A is Type` can be answered by any `Eq` instance in scope (section 3.8). That is harmless for `Type`, which has no members, but not in general.

This document and the library follow a convention **[Convention]**: *a type has at most one `Eq` in its implicit scope, and it is the type's semantic equality; a coarser equality gets a new type.* That is why `sameElements` is a plain method above, not a given, and why section 7.6 gives finite sets their own type, which carries `sameElements` as *its* only equality.

### 7.5 Workaround 2: canonical forms

Choose one representative for each equivalence class, and normalize every value to it: sort and deduplicate lists, reduce fractions. Then equivalent values become structurally equal, and structural `===` works again. This needs a normalization function, often an ordering, and discipline to apply it.

The type of normalized values is itself a subset (sorted, duplicate-free lists), so canonical forms lead back to chapter 6. Either combine them with abstraction, so that only normalized values are ever constructed, or choose a representation that is canonical by construction. For finite sets of small natural numbers, a bit mask is canonical: every bit pattern represents exactly one set, and there is nothing to normalize.

### 7.6 Workaround 3: abstraction

As with subsets, an opaque type can stand in for the quotient. Export only operations that respect the equivalence, and representation independence guarantees that clients cannot distinguish equivalent representations:

```scala
object finite:
  opaque type FinSet[A] = List[A]

  object FinSet:
    def empty[A]: FinSet[A]        = Nil
    def single[A](a: A): FinSet[A] = List(a)

    given FinSetIsEq: [A: Eq] => FinSet[A] is Eq = sameElements[A]

  extension [A: Eq](s: FinSet[A])
    def union(t: FinSet[A]): FinSet[A]               = s ++ t
    def contains(a: A): Boolean                      = s.exists(_ === a)
    def flatMapSet[B](f: A -> FinSet[B]): FinSet[B] = s.flatMap(a => f(a))
```

The obligation is precise: every exported operation must give equivalent results on equivalent inputs. `union`, `contains` and `flatMapSet` do. A general `fold` would not, because a fold over the underlying list sees the order; a fold is safe only with a commutative and idempotent combining operation, which is again a law the caller must establish. With this discipline, `FinSet[A]` is observationally the type of finite sets of `A`, an object of 𝒮 that plays the role of the quotient. **[Standard: abstraction theorem, from memory; assumed for Scala as part of A2]** And coherence is restored: `FinSet[A]` has exactly one equality, the one that means what the type is meant to mean.

### 7.7 Worked example: finitely branching relations

Putting the pieces together, the Kleisli category of `FinSet` is a Scala category of relations:

```scala
import finite.{FinSet, flatMapSet}

object FinRel extends Category:
  type Self[A, B] = A -> FinSet[B]
  type Obj        = Eq
  def identity[A: Eq]: A -> FinSet[A] = a => FinSet.single(a)
  def compose[A: Eq, B: Eq, C: Eq](g: B -> FinSet[C], f: A -> FinSet[B]): A -> FinSet[C] =
    a => f(a).flatMapSet(g)
```

Its objects are the types with decidable equality, `Obj = Eq`. Its arrows are relations in which each element is related to finitely many others, compared extensionally as sets at every argument. Composition is computable because the images are finite. And this is a category in which congruence is a real obligation: two arrows that return the same sets in different orders must give composites that do, which holds because `flatMap` of equal sets gives equal sets **[Proved]**, and which a test checks by composing arrows with shuffled and duplicated variants of themselves. Compared with chapter 5, where Rel with decidable predicates had uncomputable composition, and chapter 8, where Rel is restricted to finite types, this is the third piece of Rel that Scala can capture: arbitrary types, finitely branching relations.

### 7.8 Set and Scala

In Set, a quotient is always available, so any representation can be made exact by dividing out the redundancy. In Scala, two values are equal only if no program can tell them apart, and that cannot be declared, only arranged. The arrangements are: carry the equivalence explicitly and respect it everywhere (setoids), normalize to canonical representatives, or hide the representation behind operations that respect the equivalence (abstraction).

| Workaround | What you get | Obligation |
| --- | --- | --- |
| Setoid | an explicit equivalence, usable in tests | every function respects it; a convention |
| Canonical forms | structural equality works again | normalize everywhere, or use a canonical representation |
| Abstraction | a type that behaves like the quotient for clients | exported operations respect the equivalence; C3 |

### References for chapter 7

**Cited from memory, not consulted**

- The use of setoids in type theory as a substitute for quotient types.
- The behavior of the Scala standard library's small immutable sets.
- John C. Reynolds, "Types, abstraction and parametric polymorphism", 1983.

---

## Chapter 8. Objects must be types

### 8.1 The idea

In an ordinary category, objects can be anything: numbers, sets, points of a space, states of a machine. In a Scala category, the objects are types, possibly restricted by evidence (section 3.8). When the objects you want are not types, there are three strategies:

1. **Restrict types by evidence**, when the objects you want are types with some property.
2. **Make the objects into types**, by encoding them at the type level, when the objects are values such as numbers or states.
3. **Give up types and represent the category as data**, when the objects are only known at run time.

### 8.2 Strategy 1: evidence, revisited

Object evidence (section 3.8) restricts the objects to the types `A` for which an instance `A is Obj` exists. The evidence serves two purposes at once. It says which types are objects, and it supplies run-time information that uniform programs need about each object. The second purpose is what makes the following example work.

**Rel on finite types.** A finite type, with decidable equality, can list its values:

```scala
import tutorial.ch03.Categories.*
import Eq.given

trait Finite extends Eq:
  def all: List[Self] // every value, each exactly once

  object FiniteLaws:
    def complete(x: Self): Boolean = all.count(_ === x) == 1

object Finite:
  given BooleanIsFinite: Boolean is Finite:
    def equal(a: Boolean, b: Boolean): Boolean = a == b
    def all: List[Boolean]                     = List(false, true)
```

The law `complete` says that each value occurs exactly once. With this evidence, composing relations given as predicates is a finite search:

```scala
object FiniteRel extends Category:
  type Self[A, B] = (A, B) -> Boolean
  type Obj        = Finite
  def identity[A: Finite]: (A, A) -> Boolean = (x, y) => x === y
  def compose[A: Finite, B: Finite, C: Finite](s: (B, C) -> Boolean, r: (A, B) -> Boolean): (A, C) -> Boolean =
    (a, c) => B.all.exists(b => r(a, b) && s(b, c))
```

The evidence for the middle object `B` supplies the list to search. This is exactly the information whose absence made composition uncomputable in Proposition 5.1. The laws are the laws of Rel, computed pointwise. **[Proved]** It is also the precise sense of the lesson of section 4.5: `compose` cannot ask which type `B` is, since uniformity forbids branching on types, but it can ask `B`'s evidence for the list of its values, a value it may branch on.

There is a bonus. Between finite types, equality of arrows *is* decidable: two predicates on `(A, B)` can be compared at every pair. So for this category the laws can be checked exhaustively on small types, and an exhaustive test is a proof. **[Proved]**

### 8.3 Strategy 2: objects as types

**Singleton types and evidence: matrices.** Let the objects of Mat be the singleton types `0`, `1`, `2`, …, and let the evidence carry the dimension:

```scala
/** Evidence that a singleton type N is a dimension, with its value. */
trait Dim extends Type:
  def value: Int

object Dim:
  given SingletonIsDim: [N <: Int: ValueOf] => N is Dim:
    def value: Int = valueOf[N]

object matrices:
  /** An arrow N → M is an M × N matrix: M rows of N entries each. */
  opaque type Matrix[N, M] = Vector[Vector[BigInt]]

  object Matrix:
    def fromRows[N: Dim, M: Dim](rows: Vector[Vector[BigInt]]): Option[Matrix[N, M]] =
      if rows.length == M.value && rows.forall(_.length == N.value) then Some(rows) else None

  object Mat extends Category:
    type Self[A, B] = Matrix[A, B]
    type Obj        = Dim
    def identity[A: Dim]: Matrix[A, A] =
      Vector.tabulate(A.value, A.value)((i, j) => if i == j then BigInt(1) else BigInt(0))
    def compose[A: Dim, B: Dim, C: Dim](g: Matrix[B, C], f: Matrix[A, B]): Matrix[A, C] =
      Vector.tabulate(C.value, A.value)((i, k) => (0 until B.value).map(j => g(i)(j) * f(j)(k)).sum)
```

The dimensions in the types make composition type-check only for matching sizes. Evidence supplies the actual numbers at run time, both to build identity matrices and to run the loops. That the representation really has the dimensions its type claims is a subset condition, maintained by abstraction: the only way to obtain a `Matrix` from outside is `fromRows`, which checks, and the category's own operations, which preserve the shapes. The laws are those of matrix multiplication **[Standard]**.

**Type-level naturals and GADTs: matrices with no subset condition.** With `Z` and `S[N]` from section 4.5, a vector can be indexed by its length:

```scala
import tutorial.ch04.Snippets.{S, Z}

enum Vec[N, A]:
  case VNil[A]() extends Vec[Z, A]
  case VCons[N, A](head: A, tail: Vec[N, A]) extends Vec[S[N], A]

type VecMatrix[N, M] = Vec[M, Vec[N, BigInt]] // M rows of N entries
```

Now the shape is guaranteed by the type, and there is no invariant left to maintain. Identity and multiplication are written by recursion on value-level naturals supplied as evidence, with an evidence class that has instances for `Z` and `S[N]` as in section 4.5. The price is a slow linked representation and more complex code.

**Path-dependent types: objects created at run time.** If `val n: Int` is read from input, then `n.type` is a type, so an object can be created at run time. Evidence `n.type is Dim` can be built from the value `n` itself, or obtained through `ValueOf` **[from memory]**. This is a real form of dependent typing, and it lies outside the model **[Open]**.

**Proofs as arrows: preorders.** Section 4.5 built the order on the natural numbers with a GADT of proofs. The same idea gives any preorder that has an inductive definition: an arrow a → b is a derivation of a ≤ b, and composition is a recursive function on derivations.

### 8.4 Free categories: typed state machines

A close relative of proofs as arrows is the **free category** on a graph. Its objects are the vertices of the graph, and its arrows are the paths: finite sequences of edges, each starting where the previous one ended. Composition is concatenation, and the identity is the empty path. In Scala, a GADT of edges indexed by source and target gives a typed state machine:

```scala
final class Closed
final class Opened
final class Locked

enum Step[A, B]:
  case Open   extends Step[Closed, Opened]
  case Close  extends Step[Opened, Closed]
  case Lock   extends Step[Closed, Locked]
  case Unlock extends Step[Locked, Closed]

enum Path[A, B]:
  case Stay[A]() extends Path[A, A]
  case Then[A, B, C](first: Step[A, B], rest: Path[B, C]) extends Path[A, C]

def concat[A, B, C](p: Path[A, B], q: Path[B, C]): Path[A, C] = p match
  case _: Path.Stay[?]    => q
  case Path.Then(s, rest) => Path.Then(s, concat(rest, q))

object Paths extends Category:
  type Self[A, B] = Path[A, B]
  type Obj        = Type
  def identity[A: Type]: Path[A, A] = Path.Stay()
  def compose[A: Type, B: Type, C: Type](g: Path[B, C], f: Path[A, B]): Path[A, C] = concat(f, g)
```

The laws are the associativity and unit laws of concatenation, proved by induction on the first path. **[Proved]** Only legal sequences of steps can be written: `Path[Closed, Locked]` contains `Then(Lock, Stay())` but nothing that unlocks a door that is open. Arrows are data, so equality is decidable, in contrast with chapter 5.

Free categories have a universal property: a functor out of the free category on a graph is determined by where it sends the edges, and every assignment of arrows to edges extends to a functor **[Standard]**. In code, that functor is a fold over paths. For instance, interpreting each step as a function on some state gives a functor from `Paths` to `Total`, which runs the state machine.

### 8.5 Strategy 3: categories as data

When the objects and arrows are only known at run time, as when a workflow or a graph is loaded from configuration, the category has to be represented as data:

```scala
abstract class CategoryData:
  type Obj
  type Arr
  def src(f: Arr): Obj
  def tgt(f: Arr): Obj
  def id(a: Obj): Arr
  def compose(g: Arr, f: Arr): Option[Arr]   // defined exactly when tgt(f) equals src(g)
```

The laws become conditional: `src(id(a))` is `a`; `compose(g, f)` is defined exactly when `tgt(f)` equals `src(g)`; associativity and identity hold wherever the composites are defined.

This is not an 𝒮-category with `Obj` as its objects, for the reason already seen in section 4.5: the arrows from a to b are the subset { f : Arr | src(f) = a and tgt(f) = b }, not a type. Category theory calls a structure of this shape an **internal category**, with the object of composable pairs given by a pullback, which is itself a subset **[Standard, from memory]**. Without subsets, Scala represents the composable pairs by `Option`, so composition becomes partial and errors move to run time.

Categories as data are the right tool when the structure genuinely is data. They lose the compile-time checking of sources and targets, and their laws carry side conditions.

### 8.6 What type-level features buy

| Feature | Helps with | Cost | In the model? |
| --- | --- | --- | --- |
| Object evidence (`Obj`) | restricting objects; run-time information about objects | evidence must be threaded through | yes |
| Singleton types | naming values, such as numbers, as types | composition still cannot branch on them | no |
| Match types | computing homs for concrete objects | stuck on abstract arguments | no |
| GADTs | proofs and shapes as data; uniform composition by recursion on arrows | representation size; complexity | encodable; parametricity **[Open]** |
| Path-dependent types | objects created at run time | dependent typing | no |
| Opaque types | subsets and quotients by abstraction | proof obligation on exported operations | yes, as existential types |

### 8.7 Set and Scala

In Set, anything can be an object, and a category's structure can depend on its objects in any way. In Scala, objects are types. When the objects you want are types with a property, evidence restricts to them and supplies the run-time information composition needs. When they are values, they can be encoded as types with singleton types or GADTs, at some cost in complexity and with a step outside the model. When they are only known at run time, the category becomes data, and its typing becomes run-time checks.

### References for chapter 8

**Cited from memory, not consulted**

- Free categories on graphs and their universal property; internal categories. See Mac Lane 1998.
- `scala.ValueOf` and its synthesis for singleton types.

---

## Chapter 9. Uniformity's payoff: parametricity

### 9.1 The idea

Uniformity was presented as a constraint: a polymorphic program cannot inspect its type arguments, so it must do the same thing at every type. This chapter shows the other side. Because a polymorphic program cannot inspect its type arguments, its type alone tells you a great deal about what it does. Reynolds made this precise as **relational parametricity** **[Standard: Reynolds 1983, from memory]**, and Wadler turned it into a method for reading off equations, which he called **free theorems**, from the types of polymorphic functions **[Standard: Wadler 1989, from memory]**.

### 9.2 Examples

**The polymorphic identity.** Every total `f: [A] => A -> A` is the identity. **[Proved, given A2 below]**

*Proof.* The free theorem for this type says that for every pair of types and every total function `h: X -> Y`, `f[Y](h(x))` ≐ `h(f[X](x))`; that is, f commutes with every function. Take X to be `Unit` and h to be `_ => y` for an arbitrary total y of type Y. Since `Unit` has only one value, `f[Unit](())` is `()`. So `f[Y](y) = f[Y](h(())) ≐ h(f[Unit](())) = h(()) = y`. ∎

**Rearrangements of lists.** Every total `r: [A] => List[A] -> List[A]` commutes with `map`: `r(xs.map(h))` ≐ `r(xs).map(h)` for every `h`. **[Standard: Wadler 1989, from memory; given A2]** So `r` can only rearrange, drop or duplicate elements according to their positions; it cannot look at them. `reverse`, `take(3)` and `tail`-like functions all have this type, and the free theorem holds for each of them without being checked.

**Swaps and projections.** Every total `[A, B] => ((A, B)) -> (B, A)` is the swap, and every total `[A] => ((A, A)) -> A` is one of the two projections. **[Standard, from memory; given A2]**

### 9.3 The general statement

**Assumption A2 (parametricity).** **[Assumed]** Every total polymorphic program respects relations: if its type arguments are instantiated at two types related by any relation, and its arguments are related correspondingly, then its results are related correspondingly.

The precise statement interprets every type as a relation, built up from the structure of the type; for function types, related functions send related arguments to related results. A2 is a theorem for System F and for the formal core of appendix A **[Standard: Reynolds 1983; Wadler 1989; Pitts 2000, from memory]**. It has not been proved for Scala, which is why it is an assumption. A2 also covers the abstraction theorem used in chapters 6 and 7: clients of an abstract type cannot distinguish related implementations.

For types built from functors, the free theorem takes a particularly useful form. A total `α: [A] => F[A] -> G[A]`, where `F` and `G` have lawful `map`s, satisfies

`α[B](fa.map(h))` ≐ `α[A](fa).map(h)` for every `h: A -> B`.

Chapter 13 calls this **naturality**. So every polymorphic function between functors is natural, without any law to check. **[Standard: Wadler 1989, from memory; given A2]**

### 9.4 What it gives Scala categories

Free theorems constrain the identity and composition of every Scala-defined category, because they are polymorphic programs.

For `Total`, the identity `identity[A]: A -> A` is, by section 9.2, *the* identity function: there is no other choice. And composition `compose[A, B, C]: (B -> C, A -> B) -> A -> C` has, up to equality, only one total inhabitant, `a => g(f(a))`, since the only way to produce a `C` from an `A` with the arguments available is to apply `f` and then `g` **[Standard: the inhabitants of this type in System F, from memory; given A2]**. So there is exactly one way to make `Total` a category, and its laws are automatic.

For other categories the constraint is weaker but still real. Any `compose` for `OptionKleisli` must, at each argument, either run both functions and combine their results in the only way the types allow, or return `None` at some stage. The category laws then exclude the degenerate choices.

The most important consequence is the one stated at the end of section 9.3: natural transformations come for free. Chapter 13 builds on it.

### 9.5 What breaks parametricity

Every exclusion in C3 (section 2.3) breaks some free theorem, and the C2 exclusions break others.

| Feature | Broken free theorem |
| --- | --- |
| Type tests and pattern matching on type parameters | `notId` of section 2.3 has type `[A] => A -> A` and is not the identity |
| Casts | the same, and abstract types can be forged |
| `null` | `[A] => A -> A` could return `null`; it is not the identity |
| `eq`, `hashCode`, `toString` | `[A] => ((A, A)) -> A` could pick the argument with the smaller hash, which is neither projection uniformly |
| Reflection | any polymorphic function can inspect the class of its argument |
| Non-termination and exceptions | many free theorems need side conditions among the programs of 𝒫; in Haskell, `seq` forces conditions such as strictness of the functions involved **[Standard: Johann and Voigtländer 2004, from memory]** |
| GADT pattern matching | type refinement complicates the relational interpretation **[Open]** |
| Subtyping and `Any`'s methods | outside the model |

This table is the deepest justification of C3. Representation independence is not a matter of style. Without it, polymorphic types stop telling you what programs do.

### 9.6 Polymorphism is not set-theoretic

Reynolds proved that System F has no model in classical set theory in which the type `A => B` is interpreted as the set of *all* functions from A to B **[Standard: Reynolds 1984, from memory]**. That is a statement about Set, not about 𝒮, but it explains a precise difference between the two.

Consider Val(`[A] => A -> A`). By section 9.2 it has exactly one element, the identity. Now compare it with the family of all choices of a function X → X for every set X, the product of all the sets Val(X => X). That product contains a different, wildly non-uniform family for every way of choosing an endomap of each type separately. So Val does not turn polymorphic types into products over all types. **[Proved, given A2]** A polymorphic type contains only the *uniform* families, the ones that one program computes at every type. In category-theoretic terms, the polymorphic type behaves like an **end**, a construction that picks out the families compatible with all arrows, rather than like a product. This is something 𝒮 has and Set does not have in the same form: a type of uniform families, together with free theorems about its elements.

### 9.7 The uniformity question

Section 4.5 distinguished 𝒮-categories, whose structure can be chosen object by object, from Scala-definable ones, whose structure is one polymorphic program. The same distinction arises for natural transformations. A family of arrows α_A : F(A) → G(A), chosen separately for each type A in the meta-language, may be natural without being given by a single polymorphic program. The proof of section 9.2 shows that, for the identity type, every natural family is uniform: any natural family of maps A → A is the identity at every A. Whether every natural family between Scala-definable functors is, at each type, equal (≐) to the instance of a single polymorphic program is a question we have not seen settled **[Open]**. The answer matters for chapter 13: it decides whether the polymorphic function type is the type of *all* natural transformations or only of the uniform ones.

### 9.8 Set and Scala

In Set, a family of functions indexed by all sets can be anything, and nothing about a function's type constrains its behavior. In Scala, polymorphic programs are uniform, and their types imply equations about them. These free theorems hold without being tested, provided the contract holds, and they fail in specific, predictable ways when it does not.

### References for chapter 9

**Cited from memory, not consulted**

- John C. Reynolds, "Types, abstraction and parametric polymorphism", *Information Processing 83*, 1983.
- John C. Reynolds, "Polymorphism is not set-theoretic", *Semantics of Data Types*, Lecture Notes in Computer Science 173, Springer, 1984.
- Philip Wadler, "Theorems for free!", *FPCA 1989*.
- Andrew M. Pitts, "Parametric polymorphism and operational equivalence", 2000.
- Patricia Johann and Janis Voigtländer, "Free theorems in the presence of seq", *POPL 2004*.

---

## Chapter 10. One kind per class

### 10.1 The idea

The objects of a `Category` instance are the types of kind \*, because `identity[A]` quantifies over such types. Many important categories have objects of a different kind. The category of functors on 𝒮 has type constructors such as `List` and `Option` as objects, of kind \* → \*. The definitions of monads and of "monoids in the category of endofunctors" live there.

### 10.2 Categories of type constructors

A category whose objects are type constructors needs its own class, with a `Self` of a higher kind:

```scala
abstract class Category1 extends caps.Pure:
  type Self[F[_], G[_]]
  final type -->[F[_], G[_]] = Self[F, G]

  def identity[F[_]]: F --> F
  def compose[F[_], G[_], H[_]](g: G --> H, f: F --> G): F --> H

object NaturalTransformations extends Category1:
  type Self[F[_], G[_]] = [A] => F[A] -> G[A]
  def identity[F[_]]: [A] => F[A] -> F[A] = [A] => (x: F[A]) => x
  def compose[F[_], G[_], H[_]](g: [A] => G[A] -> H[A], f: [A] => F[A] -> G[A]): [A] => F[A] -> H[A] =
    [A] => (x: F[A]) => g[A](f[A](x))
```

The arrows of `NaturalTransformations` are polymorphic functions, written with Scala 3's polymorphic function types. Its laws hold for the same reasons as those of `Total`, at every type at once. **[Proved]** Its objects are *all* type constructors of kind \* → \*, not only functors. Restricting to functors needs evidence, as in section 3.8, and that evidence needs a class of its own too, since `Type` describes types of kind \*. With that restriction, chapter 9 shows that every arrow is natural for free, so this is the category of functors and natural transformations, as far as uniform ones are concerned (section 9.7).

### 10.3 No polymorphism over kinds

Scala 3 has a limited form of kind polymorphism: a type parameter bounded by `AnyKind` can be instantiated with a type of any kind. But such a parameter cannot be applied to arguments, so it cannot be used to write `identity` and `compose` once for all kinds **[Standard: Scala 3 reference, "Kind Polymorphism", from memory]**. The `is` type of the modularity proposal accepts `Self` members of any kind (it is declared with an `AnyKind` bound [Scala type classes, checked]), so type classes of any single kind are easy to write; what is missing is a single definition that works at every kind.

The consequence is duplication. Each kind needs its own category class, its own laws and its own instances. `Category` and `Category1` are two different classes, and a construction that works for both, such as the opposite category, has to be written twice.

### 10.4 What this means for the slogans

"A monad is a monoid in the category of endofunctors" is a precise statement in category theory: there is a general notion of a monoid in any monoidal category, and instantiating it with the category of endofunctors, whose tensor is composition of functors, gives exactly the definition of a monad. In Scala, the general notion cannot be written once, because a monoidal category whose objects have kind \* → \* needs a different class from one whose objects have kind \*. What can be written is the specialization by hand: a unit `[A] => A -> F[A]` and a multiplication `[A] => F[F[A]] -> F[A]`, with laws that are the monoid laws read at kind \* → \*. Chapter 15 does exactly this, and the library's `Monoid` and `Monad` are accordingly two classes. The slogan is true, but in Scala it is a comparison between two definitions, not an instance of one.

### 10.5 Set and Scala

In mathematics, categories of categories, of functors and of functor categories are all just categories, and one definition covers them all. In Scala, a definition is written at one kind. Each new kind needs a new class.

### References for chapter 10

**Consulted while writing this chapter**

- Scala 3 reference: "Better Support for Type Classes" (for the definition of `is`). https://scala-lang.org/api/docs/experimental/typeclasses.html

**Cited from memory, not consulted**

- Scala 3 reference: "Kind Polymorphism".

---
# Part III. Working with categories

Parts I and II were about what a Scala category is and what that commits you to. This part develops the standard tools of category theory, functors, natural transformations, universal constructions, monads, adjunctions and recursion, in that light. From here on, the code uses the library `parrot.category`, whose classes are the ones Part I wrote by hand, grown to cover these tools. Its laws are tested, and every **[Tested]** label in this part refers to a row of the library's law status table (chapter 22).

## Chapter 11. Encoding categories in Scala 3

### 11.1 The idea

Chapter 3 wrote a category as a class with a type member `Self` for its arrows and an object, such as `Total` or `OptionKleisli`, for each instance. That shape served Part I well, because every construction there was about one category at a time. The tools of this part relate several: a functor goes from one category to another, a monoidal structure lives on a category, a monad's arrows form a new category on top of an old one. Three problems from Parts I and II show what the encoding has to handle.

1. **A structure on something else needs to name it.** A functor F : 𝒞 → 𝒟 (Definition 1.3) mentions the arrows of 𝒞 and of 𝒟 in the type of its arrow map. A class for functors therefore needs two categories inside it, as values whose types and members it can refer to.
2. **One thing can carry several structures.** 𝒮 has products and coproducts (chapter 14), two different ways of combining two objects into one. A ring is two monoids on one carrier. A parser (chapter 20) is a category with several additional structures at once. If structures were found by their carrier, as type classes usually are, there would be no way to say which one is meant.
3. **Objects need evidence**, as in section 3.8, and the evidence has to reach the programs that need it without the programmer passing it by hand.

This chapter explains how the library solves each problem with features of Scala 3 that are still experimental, and what each solution costs. It introduces no new mathematics. Readers who want only the mathematics can skim it and return when a later chapter refers back.

### 11.2 Bases are parameters

The first attempt at a functor class follows chapter 3: a type member for the object map and type members for the two categories.

```scala unit=TypeMembers
abstract class Category:
  type Self[_, _]
  def identity[A]: Self[A, A]
  def compose[A, B, C](g: Self[B, C], f: Self[A, B]): Self[A, C]

abstract class Functor:
  type Self[_]
  type C[_, _]   // the arrows of the source category
  type D[_, _]   // the arrows of the target category
  def map[A, B](f: C[A, B]): D[Self[A], Self[B]]
```

The functor can name the *types* of the arrows of 𝒞 and 𝒟, but not the categories themselves: nothing gives it the identity of 𝒞 or the composition of 𝒟, which its laws need. Adding them as type-class evidence, found by the type `C`, works for one category per arrow type, and fails as soon as two categories share an arrow type, which is the situation of problem 2. The library's previous encoding went this way and needed type casts to connect a category value with the type that named it.

Scala 3 offers a better tool. A class parameter declared `val` is a **stable path**: inside the class, its type members can be named and its members imported, as `C.Self` or `D.identity`. And a parameter declared `tracked` keeps the precise type of the argument in the type of the instance:

```scala library
import parrot.category.*

abstract class MyFunctor(tracked val C: Category, tracked val D: Category):
  type Self[_]
  def map[A: C.Obj, B: C.Obj](f: C.Self[A, B]): D.Self[Self[A], Self[B]]

object OptionMap extends MyFunctor(Total, Total):
  type Self[A] = Option[A]
  def map[A: Type, B: Type](f: A -> B): Option[A] -> Option[B] = _.map(f)

val lengths: Option[String] -> Option[Int] = OptionMap.map[String, Int](_.length)
```

Because `C` is tracked, the type of `OptionMap.C` is `Total.type`, not just `Category`, so the compiler knows that `OptionMap.C.Self[A, B]` is `A -> B` and that `C.Obj` is `Type`. That is why `map` can be implemented with the types of 𝒮 and why `lengths` type-checks. Without `tracked`, the same code does not compile, because outside the class nothing is known about the categories:

```scala unit=Untracked fails library
import parrot.category.*

abstract class MyFunctor(val C: Category, val D: Category):
  type Self[_]
  def map[A: C.Obj, B: C.Obj](f: C.Self[A, B]): D.Self[Self[A], Self[B]]

object OptionMap extends MyFunctor(Total, Total):
  type Self[A] = Option[A]
  def map[A: Type, B: Type](f: A -> B): Option[A] -> Option[B] = _.map(f)
```

The library's `Functor`, `Bifunctor`, `Profunctor`, `Monoidal`, `Strong` and every other structure on something else take what they are built on as `tracked` parameters. A refinement passes its parameter on under the same name: `Promonad(tracked override val K: Category)` extends `Endoprofunctor(K, Total)`. That is why structures are abstract classes and not traits: a Scala trait cannot pass arguments to a parent trait. Type classes without parameters, such as `Type`, `Eq` and `Observable`, are traits. And a constraint between parameters is a refinement of a later parameter's type, checked when the instance is created: `Strong.Bistrong` takes a profunctor `P { val K2: K1.type }` from a category to itself and a symmetric monoidal structure `M { val K: P.K1.type }` on that category, so a strength over the wrong category is a type error.

### 11.3 A carrier, or a name

Problem 2 asks when a structure should be found by its carrier, the way `given Int is Eq` is found by `Int`, and when it should be named. The library's rule:

- **A structure with its own carrier has a `Self`**, and instances can be found by carrier: `Category` (its arrows), `Functor` (its object map), `Monad`, `Monoid`, `Eq`, `Observable`.
- **A structure on something else has no `Self`** and is always named: `Monoidal`, `Strong`, `Restriction`, `Traced`. 𝒮 carries two monoidal structures, and they are the objects `Total.Product` and `Total.Coproduct`:

```scala library
import parrot.category.*

val swap: ((Int, String)) -> (String, Int)       = Total.Product.braid[Int, String]
val mirror: Either[Int, String] -> Either[String, Int] = Total.Coproduct.braid[Int, String]
```

Both are called `braid`, both act on 𝒮, and nothing about the carrier tells them apart; the name does.

Combinations of structures are not expressed by inheritance either. A class that extended both a product structure and a coproduct structure would inherit two members called `Tensor`, two called `I` and two called `braid`, which is wrong even where the compiler accepts it. Instead, a combination is a **bundle**: a class that takes the structures as `tracked` parameters and offers their operations, possibly with laws that connect them. The library has two bundles. `Freyd` (chapter 17) combines a category of arrows with a strength. `ParserAlgebra` (chapter 20) combines everything a parser is made of.

### 11.4 Evidence, and how it is found

Problem 3 is solved as in section 3.8: a category declares `type Obj <: Type`, and its identity and composition take context bounds `[A: Obj]`. The library adds three rules that matter in practice.

- **Evidence is passed only through context bounds**, never through an explicit `using` clause before the value parameters. Scala resolves a `using` clause where it appears, so a clause before the arrows would be resolved before the arrows had told the compiler which types are meant. Context bounds are placed after the value parameters, so infix code such as `f >>> g` infers every type.
- **Evidence that chooses an object is a parameter.** A monoidal structure is on its unit object as much as on its tensor, so it takes the unit's evidence as a `tracked` parameter, `Monoidal(K, U, T)`, and the unit object is the type that evidence is about, `I = U.Self`. 𝒮 has two units, `Unit` for its products and `Nothing` for its coproducts, so implicit search could no more choose the unit than the tensor. `Monoidal` offers the evidence to its clients as a given, `IIsObj`.
- **An instance names its own evidence**, as `Type.TIsType`, instead of searching for it. A structure that offers evidence to its clients, such as `Monoidal.TensorIsObj`, would otherwise be found by its own definition and call itself.

Infix code needs one more rule: **every operation has one operator name.** `>>>` composes, in a category and in a category of arrows (chapter 17) alike, `***` is the tensor of a monoidal structure, `&&&` and `|||` pair and copair, `**` runs two effectful arrows side by side, `=?=` asks an `Observable` whether two values agree. Operators of the same name from two imports form an overload, which Scala resolves by the type of the arrow, so pure and effectful arrows can be composed side by side with `>>>`. The one exception is a value that is an arrow of two structures at once: an arrow A → M(B) of a Kleisli promonad on 𝒮 is also a function, so for it both `>>>` apply, and Scala reports an ambiguity or picks one and rejects the argument. Code about such arrows imports only one `>>>` and calls the other composition by its name. And every operator is only syntax: it passes its arguments, in order, to a named method that holds the logic, so `p >>> q` is `andThen(p, q)` and `p ** q` is `parallel(p, q)`, and every operation can be found, documented and exported by its name. With these names, code reads like the mathematics:

```scala library
import parrot.category.*
import Total.>>>
import Total.Product.{***, &&&}

val f: Int -> Int        = _ + 1
val g: Int -> String     = _.toString
val h: ((Int, String)) -> String = (n, s) => s * n

val both: Int -> (Int, String) = f &&& g
val pipeline: Int -> String    = both >>> h
val parallel: ((Int, Int)) -> (Int, String) = f *** g
```

**Names for arrows and carriers.** Type members get short names too, so that signatures read like the definitions. Every class with a carrier names it: `Hom` for the morphisms of a category, `F` for the object map of a functor or bifunctor, `P` for a profunctor or promonad, `M` for a monad or monoid, `C` for a comonoid. Morphisms are written infix, and the arrow says which category they belong to: `A --> B` in the category at hand, `A ->> B` in a second one, `A ==> B` in a target category, `A ~~> B` in an opposite one. These three-symbol arrows name a role; the two concrete categories have two-symbol arrows: `A -> B` in 𝒮 and `A ~> B` in 𝒫. A bifunctor's arrow map therefore reads `bimap(f: A1 --> A2, g: B1 ->> B2): F[A1, B1] ==> F[A2, B2]`. Objects are combined infix as well: `A * B` for a monoidal tensor, `A + B` for a coproduct, `B ^ A` for the internal hom from A to B, as in the exponential Bᴬ, and `A <-> B` for an isomorphism. A structure brings the names of the structures it is built on into scope by importing them, renaming where two categories meet, as in `import M.K.{Obj, -->}` or `import D.--> as ==>`, so that `M.K.Self[A * C, B * D]` becomes `(A * C) --> (B * D)`.

### 11.5 Laws, tests and the status table

Every structure in the library states its laws as `Boolean` methods inside the class, in an object such as `CategoryLaws`, exactly as chapter 3 did. Equations are checked with an `Observable` (section 3.3): two values agree when finitely many observations of them agree. Inequations, which appear in chapter 20, are checked with its ordered counterpart, a `Preorder`. A law with a premise, such as congruence, takes values that satisfy the premise by construction.

The library's tests run one generic specification per structure against every instance, with arrows produced by generators that exercise the interesting cases (failure, effects, loops that stop) and observations whose sample points are chosen afresh for every property. Each run writes the outcome of every law check into the **law status table**, `docs/law-status.md`. The table also lists *counterexamples*: laws that are known to fail for an instance, each checked by a test that searches for a counterexample and must find one. A label **[Tested]** in this document means that the law has a row marked "Tested" in that table.

### 11.6 What the encoding costs

The encoding rests on experimental features: the `is` syntax and `tracked` parameters of Scala 3's modularity proposal, and capture checking for the pure function type `->` [Scala modularity, from memory]. Four costs are worth knowing.

- **A false warning.** The compiler's initialization checker (`-Wsafe-init`) warns that a `tracked` parameter "may be accessed before it is initialized" when a *class* passes it on to a parent class that has parameters. At run time it is always initialized. Objects do not trigger the warning. The library's build turns the checker off rather than silencing it on each class where it appears **[Checked: Scala 3.10.0]**.
- **A surprising given.** An instance whose `Self` is `Nothing`, such as an `Eq` for the empty type, is found by the compiler for *every* query of the same type class, because `Nothing` is a subtype of everything. The library therefore offers `Eq.NothingIsEq` as a plain value, not as a given **[Checked: Scala 3.10.0]**.
- **A false unused warning.** A type imported under a new name, as in `import D.--> as ==>`, is reported as unused even where signatures use it. The library's build leaves imports out of the unused checks rather than silencing the warning on each renamed import **[Checked: Scala 3.10.0]**.
- **Tool support.** Not every tool that parses Scala understands `tracked` yet out of the box; Pants requires the in-repo `scala_override` plugin to parse `tracked` parameters **[Checked]**.

None of these is a cost of the mathematics. Each is the price of using a language feature early.

### 11.7 Set and Scala

In mathematics, a functor between two categories, a monoidal structure on a category, or a category with three extra structures is written down by naming its parts. In Scala, the same is possible once the parts are values: `tracked` parameters let a structure name what it is built on, names distinguish structures that share a carrier, and bundles combine them without inheritance. What remains specific to Scala is the bookkeeping that Part I already met, namely evidence for objects, and the uniformity of every program involved.

### References for chapter 11

**Cited from memory, not consulted**

- The Scala 3 reference pages on the modularity improvements (`tracked` parameters, the `is` syntax for type classes) and on capture checking.

---

## Chapter 12. Functors, bifunctors and profunctors

### 12.1 The idea

A functor (Definition 1.3) sends objects to objects and arrows to arrows, preserving identities and composition. Section 4.6 added the requirement that makes it a Scala functor: its action on arrows is a program, an arrow of 𝒮 between hom types. This chapter writes functors with the encoding of chapter 11, and then meets two variations that appear constantly in programs: functors of two arguments, and functors that reverse the direction of some arrows.

### 12.2 Functors between categories

The library's functor takes its two categories as parameters:

```scala unit=Shape library
import parrot.category.{Category, Type}

abstract class Functor(tracked val C: Category, tracked val D: Category):
  import C.-->
  import D.--> as ->>                               // the arrows of the target category
  type Self[_]
  final type F = Self                               // the object map
  def objects[A: C.Obj]: F[A] is D.Obj              // objects go to objects
  def map[A: C.Obj, B: C.Obj](f: A --> B): F[A] ->> F[B]   // the arrow map
```

`objects` is new compared with chapter 3: the object map must send objects of 𝒞 to objects of 𝒟, and when objects carry evidence, the functor must provide it. The laws are those of Definition 1.3, checked with an `Observable` of 𝒟's arrows:

- `FunctorLaws.identity`: F(id) = id
- `FunctorLaws.composition`: F(g ∘ f) = F(g) ∘ F(f)
- `FunctorLaws.congruence`: if f = f′ then F(f) = F(f′)

**Endofunctors on 𝒮.** Most of what programmers call functors are functors from a category to itself, **endofunctors**, and most of those are functors from 𝒮 to itself. The library's `Endofunctor(K)` is `Functor(K, K)`. `Option` is one, `Endofunctor.OptionIsEndofunctor`, and the monad `Monad.OptionIsMonad` of chapter 15 is structure on it:

```scala library
import parrot.category.*

val O                                  = Endofunctor.OptionIsEndofunctor
val lengths: Option[String] -> Option[Int] = O.map[String, Int](_.length)
```

**A functor between different categories.** Including the total programs among all programs is a functor from 𝒮 to 𝒫 (Proposition 2.9). It is the identity on objects, and on arrows it forgets the promise of totality:

```scala library
object Inclusion extends Functor(Total, Partial):
  type Self[A] = A
  def objects[A: Type]: A is Type                = Type.TIsType
  def map[A: Type, B: Type](f: A -> B): A ~> B = Partial.fromTotal(f)
```

Its laws hold because `Partial.fromTotal(f)` is `f` itself; Proposition 2.9 says it is also faithful. The library defines it as `Partial.Inclusion`.

**Non-examples.** A `map` for `List` that also reverses the list breaks the identity law. A `map` that counts how often it is called breaks C1 and does not have the type `A -> B` under capture checking. A `map` for `Partial` that tries to decide whether its argument terminates cannot be written at all.

**A free theorem.** For a parametric `map` on an endofunctor of 𝒮, the composition law follows from the identity law **[Standard: a consequence of parametricity, from memory; given A2]**. In practice, checking the identity law is the important test.

### 12.3 Bifunctors

Pairs and tagged unions are functorial in *two* arguments: given f : A → A₂ and g : B → B₂, there is an arrow (A, B) → (A₂, B₂) that applies f on the left and g on the right, and similarly for `Either`. A functor of two arguments is called a **bifunctor**. The definition needs no new ideas: a bifunctor F : 𝒞₁ × 𝒞₂ → 𝒟 assigns an object F(A, B) to two objects and an arrow F(f, g) to two arrows, preserving identities and composition in both arguments at once.

**Definition 12.1 (bifunctor).** A bifunctor F from 𝒞₁ and 𝒞₂ to 𝒟 consists of an object F(A, B) of 𝒟 for objects A of 𝒞₁ and B of 𝒞₂, and an arrow F(f, g) : F(A, B) → F(A₂, B₂) of 𝒟 for arrows f : A → A₂ of 𝒞₁ and g : B → B₂ of 𝒞₂, such that F(id, id) = id and F(f₂ ∘ f₁, g₂ ∘ g₁) = F(f₂, g₂) ∘ F(f₁, g₁).

```scala library
val pairs: ((Int, String)) -> (Long, Boolean) =
  Total.Tuple2IsBifunctor.bimap[Int, String, Long, Boolean](_.toLong, _.isEmpty)

val tags: Either[Int, String] -> Either[Long, Boolean] =
  Total.EitherIsBifunctor.bimap[Int, String, Long, Boolean](_.toLong, _.isEmpty)
```

Mathematicians usually define a bifunctor as a functor out of the **product category** 𝒞₁ × 𝒞₂, whose objects are pairs of objects and whose arrows are pairs of arrows, composed componentwise. The library has the product, `Category.Product(C1, C2)`, but a bifunctor still takes its categories separately, `Bifunctor(C1, C2, D)`, and implements `bimap`. The two descriptions are related by a construction rather than by inheritance: `functor` reads a bifunctor as a functor out of the product, in the same way as `category` reads a promonad as a category (chapter 17). The bifunctor laws are stated once, as the functor laws of `functor`.

```scala library
val pairsAsFunctor = Total.Tuple2IsBifunctor.functor
import pairsAsFunctor.C.given

val bothLengths: ((String, String)) -> (Int, Int) =
  pairsAsFunctor.map[(String, String), (Int, Int)]((_.length, _.length))
```

Why not let `Bifunctor` extend `Functor` directly? In Scala, an object of 𝒞₁ × 𝒞₂ has to be a single type, the pair type `(A1, A2)`, and the type of its arrows has to be computed from it: `(C1.-->[A1, B1], C2.-->[A2, B2])`. The only way to take a type apart at the type level is a **match type**, `Fst[(A1, A2)] = A1`. The type of arrows cannot depend on the evidence for an object, which is a value, and selecting a type member of an abstract type is not allowed, because it is unsound. So the product needs match types, and a bifunctor that extended `Functor` would carry them in the signatures that every instance implements. As a construction, they stay inside `Category.Product` and `functor`. Generic code never needs them to reduce either, because the evidence that a pair type is an object speaks about `Fst[X]` and `Snd[X]` directly; they reduce only where a concrete pair type such as `(String, String)` appears. A class for categories whose objects are pairs of types would avoid match types, at the price of the duplication described in chapter 10.

The same two type constructors are bifunctors on 𝒫 as well, `Partial.Tuple2IsBifunctor` and `Partial.EitherIsBifunctor`. On 𝒫, `bimap(f, g)` on a pair runs f, then g, so if either does not terminate, neither does the pair. That small fact is the reason pairs are not products in 𝒫 (chapter 14). The bifunctor laws for all four instances are **[Tested]**.

### 12.4 Contravariance and profunctors

A predicate `A -> Boolean` can be pulled back along a function `f: B -> A` to a predicate on `B`: first apply f, then the predicate. The direction is reversed: an arrow B → A gives a map from predicates on A to predicates on B. A functor that reverses arrows is a functor out of the **opposite category** (section 3.7), and is called **contravariant**.

Function types do both at once. A function `A1 -> B1` can be pre-composed with `f: A2 -> A1` and post-composed with `g: B1 -> B2`, giving `A2 -> B2`. The first argument is contravariant and the second covariant. Such a functor is a **profunctor**.

**Definition 12.2 (profunctor).** A profunctor P, valued in 𝒱, is a bifunctor P : 𝒦₁ᵒᵖ × 𝒦₂ → 𝒱. Its action on arrows is written P(f, g), for f : A₂ → A₁ of 𝒦₁ and g : B₁ → B₂ of 𝒦₂, and maps P(A₁, B₁) to P(A₂, B₂). A profunctor on a category 𝒦, a bifunctor P : 𝒦ᵒᵖ × 𝒦 → 𝒱, is an **endoprofunctor**.

The library's `Profunctor(K1, K2, V)` is exactly `Bifunctor(K1.op, K2, V)`, with a method `dimap` that spells out the variance, and its `Endoprofunctor(K, V)` is `Profunctor(K, K, V)`. The most important example is the **hom profunctor** of a category, an endoprofunctor whose value at (A, B) is the type of arrows A → B and whose action pre- and post-composes. For 𝒮 it is `Total.Functions`:

```scala library
val f: Int -> String = _.toString
val g: String -> Int = _.length
val h: Int -> Int    = Total.Functions.dimap[String, String, Int, Int](f, g)(_ + "!")
```

`h` computes `g(f(n) + "!")`: the argument function sits between the two adapters. Profunctors are the right way to think about any kind of arrow that consumes one type and produces another: parsers, lenses, Kleisli arrows. Chapter 17 builds on them.

### 12.5 What the theory guarantees

A lawful functor preserves every equation between composites. In particular, `map` fusion, rewriting `x.map(f).map(g)` as `x.map(f andThen g)`, is sound for every lawful functor, and only for lawful ones. The same holds for `bimap` and `dimap` in each argument. Tests of the identity law, together with parametricity, give good evidence for both laws.

### 12.6 Set and Scala

In Set, a functor can send each object anywhere and act on arrows by any function that respects composition. In Scala, a functor's object map is a type constructor and its arrow map is a program, which makes every Scala functor an 𝒮-functor and gives it free theorems. Functors of two arguments and functors that reverse arrows need no new ideas, only the opposite category and a second argument.

### References for chapter 12

**Cited from memory, not consulted**

- Saunders Mac Lane, *Categories for the Working Mathematician*, 1998: bifunctors, the opposite category.
- The derivation of the functor composition law from the identity law by parametricity.

---

## Chapter 13. Natural transformations, Yoneda and equivalence

### 13.1 The idea

Functors are maps between categories. Natural transformations are maps between functors.

**Definition 13.1 (natural transformation).** Let F, G : 𝒞 → 𝒟 be functors. A **natural transformation** α : F ⇒ G assigns to every object a of 𝒞 an arrow α_a : F(a) → G(a) of 𝒟, its **component** at a, such that for every arrow f : a → b,

G(f) ∘ α_a = α_b ∘ F(f).

The equation is the **naturality square**: transforming and then mapping gives the same result as mapping and then transforming. With natural transformations as arrows, the functors from 𝒞 to 𝒟 form a category, the **functor category**, written [𝒞, 𝒟].

### 13.2 In Scala

A natural transformation between endofunctors of 𝒮 is a polymorphic function `[X] => F[X] -> G[X]`: one program that works at every type. The naturality square is a law, stated with the library's `Functor` and checked with an `Observable`:

```scala library
import parrot.category.*

/** Endofunctors of 𝒮. */
type Endo = Endofunctor { val K: Total.type }

def naturality[A, B](F: Endo, G: Endo)(alpha: [X] => F.F[X] -> G.F[X], fa: F.F[A], h: A -> B)(
    using G.F[B] is Observable): Boolean =
  G.map[A, B](h)(alpha[A](fa)) =?= alpha[B](F.map[A, B](h)(fa))

object ListFunctor extends Endofunctor(Total):
  type Self = List
  def objects[A: Type]: List[A] is Type                       = Type.TIsType
  def map[A: Type, B: Type](f: A -> B): List[A] -> List[B] = _.map(f)

val headOption: [X] => List[X] -> Option[X] = [X] => (xs: List[X]) => xs.headOption

val checked: Boolean =
  naturality(ListFunctor, Endofunctor.OptionIsEndofunctor)(headOption, List(1, 2, 3), (n: Int) => n * 2)
```

By A2, every polymorphic function between functors of 𝒮 is natural (section 9.3). So `headOption`, `reverse`, `flatten` and every other polymorphic function of this shape satisfy the naturality law without it being checked. The law is still worth testing, because a violation reveals a breach of the contract, such as a type test.

The functor category of endofunctors on 𝒮, with polymorphic functions as arrows, is the category `NaturalTransformations` of chapter 10, restricted to functors. Its hom between `F` and `G` is the type `[X] => F[X] -> G[X]`. That this hom is a type at all is special to 𝒮: in category-theoretic terms it is an end, and its existence as a type is what polymorphism provides (section 9.6). For a category whose objects are restricted by evidence, or for a general 𝒮-category, the natural transformations are families indexed by objects, and no single type collects them. So functor categories are, in general, not Scala categories. **[Open in general; true in each case examined in this document]**

### 13.3 The Yoneda lemma

The Yoneda lemma is often called the most important result in elementary category theory. In its Set-based form, it says that for every functor F : 𝒞 → Set and object a, the natural transformations from 𝒞(a, −) to F correspond exactly to the elements of F(a) **[Standard: Mac Lane 1998, from memory]**.

In Scala, with `F` a lawful endofunctor of 𝒮:

```scala library
def toYoneda[A](F: Endo)(fa: F.F[A]): [B] => (A -> B) -> F.F[B] =
  [B] => (f: A -> B) => F.map[A, B](f)(fa)

def fromYoneda[A](F: Endo)(y: [B] => (A -> B) -> F.F[B]): F.F[A] =
  y[A](a => a)
```

**Proposition 13.2.** `toYoneda` and `fromYoneda` are inverse to each other, so `[B] => (A -> B) -> F[B]` ≅ `F[A]`. **[Proved, given A2]**

*Proof.* `fromYoneda(toYoneda(fa))` is `F.map(a => a)(fa)`, which is `fa` by the identity law. In the other direction, `toYoneda(fromYoneda(y))` is `[B] => f => F.map(f)(y[A](a => a))`. By parametricity, y is natural, so `F.map(f)(y[A](a => a))` ≐ `y[B](f ∘ (a => a))` = `y[B](f)`. So the composite is y. ∎

The lemma has practical uses. The type `[B] => (A -> B) -> F[B]` represents an `F[A]` as a function that is waiting to be told how to transform the result, so repeated `map`s on it compose functions instead of rebuilding structures. Its dual, the **co-Yoneda** representation, packages a value `F[B]` for some hidden `B` with a function `B -> A`. Scala 3 has no syntax for existential types, but an abstract type member is exactly an existential:

```scala library
abstract class Coyoneda[F[_], A]:
  type B
  val fb: F[B]
  val k: B -> A
```

Mapping over a `Coyoneda` just composes `k`, so any number of `map`s can be fused into one, performed when the value is finally converted back to `F[A]`.

### 13.4 Equivalence of categories

When are two categories "the same"? Isomorphism of categories, functors that are inverse to each other on the nose, is too strict, because it is sensitive to how many isomorphic copies of each object there are.

**Definition 13.3 (equivalence).** An **equivalence** between categories 𝒞 and 𝒟 is a pair of functors F : 𝒞 → 𝒟 and G : 𝒟 → 𝒞 with natural isomorphisms G ∘ F ≅ Id and F ∘ G ≅ Id.

Equivalently, F is an equivalence when it is full, faithful, and **essentially surjective**: every object of 𝒟 is isomorphic to some F(a) **[Standard: Mac Lane 1998, from memory]**.

This makes precise two claims made earlier.

- **The two encodings of a monoid are equivalent** (section 3.8). The functor from the one-object category to the constant category sends the single object to itself and every arrow to itself. It is full and faithful, since both homs are the whole monoid, and essentially surjective, since every object of the constant category is isomorphic to the single one. **[Proved]**
- **Partial functions and Kleisli arrows of `Option` are equivalent** (Addendum 2.A), in the Set-based version **[Standard, from memory]**. Chapter 18 explains why the Scala versions are *not* equivalent: 𝒫's partiality cannot be inspected, `Option`'s can.

### 13.5 Set and Scala

In Set, a natural transformation is any family of functions satisfying the naturality squares. In Scala, the polymorphic functions between functors are natural for free, and their type exists as an object. Whether *every* natural family is polymorphic in this sense is the uniformity question of section 9.7.

### References for chapter 13

**Cited from memory, not consulted**

- Saunders Mac Lane, *Categories for the Working Mathematician*, 1998: natural transformations, the Yoneda lemma, equivalence of categories.

---

## Chapter 14. Universal constructions and monoidal structure

### 14.1 The idea

Many types are characterized not by what their values look like but by how arrows go in and out of them. Category theory calls such a characterization a **universal property**.

**Definitions 14.1.** In a category 𝒞:

- A **terminal object** 1 has exactly one arrow from every object.
- An **initial object** 0 has exactly one arrow to every object.
- A **product** of objects A and B is an object A × B with arrows π₁ : A × B → A and π₂ : A × B → B such that for every pair of arrows f : X → A and g : X → B there is exactly one arrow ⟨f, g⟩ : X → A × B with π₁ ∘ ⟨f, g⟩ = f and π₂ ∘ ⟨f, g⟩ = g.
- A **coproduct** A + B is the same with all arrows reversed: injections ι₁ : A → A + B and ι₂ : B → A + B, and for every f : A → X and g : B → X exactly one [f, g] : A + B → X with [f, g] ∘ ι₁ = f and [f, g] ∘ ι₂ = g.
- In a category with products, an **exponential** of B by A is an object A ⇒ B with an arrow ev : (A ⇒ B) × A → B such that every arrow h : X × A → B is ev ∘ (Λh × id) for exactly one arrow Λh : X → (A ⇒ B).

A category with a terminal object, all products and all exponentials is **cartesian closed**. With an initial object and coproducts as well, it is **bicartesian closed**.

Objects defined by a universal property are unique up to a unique isomorphism. For example, if 1 and 1′ are both terminal, the unique arrows 1 → 1′ and 1′ → 1 compose to arrows 1 → 1 and 1′ → 1′, which must be the identities because each hom has only one arrow. **[Proved]** This is why "the" product is well defined.

### 14.2 In 𝒮

**Proposition 14.2.** 𝒮 is bicartesian closed: **[Proved]**

- `Unit` is terminal. Every total function into `Unit` returns `()`, so any two are equal by Definition 2.5.
- `Nothing` is initial: `Nothing` has no total values, so any two functions out of it agree on every total argument.
- `(A, B)` is a product, with `_._1` and `_._2` as projections and `x => (f(x), g(x))` as ⟨f, g⟩. Uniqueness: if h satisfies both equations, then h(x) has components f(x) and g(x), so h ≐ ⟨f, g⟩.
- `Either[A, B]` is a coproduct, with `Left` and `Right` as injections and `_.fold(f, g)` as [f, g]. Uniqueness uses case analysis on the two constructors, which C3 makes exhaustive by excluding `null`.
- `A -> B` is an exponential, with `ev` the application of a function to an argument and Λh the curried form of h.

The last item is the precise form of the "three roles" of section 2.1: arrows A → B correspond to arrows `Unit` → `(A -> B)`, that is, to values of the function type.

In the library these are three objects: `Total.Product`, `Total.Coproduct` and `Total.Exponential`. Their laws, which are the universal properties above written as equations, are **[Tested]**:

```scala library
import parrot.category.*
import Total.Product.{fst, snd, &&&}
import Total.Coproduct.{inl, inr, |||}

val f: Int -> String = _.toString
val g: Int -> Boolean = _ > 0

val paired: Int -> (String, Boolean)   = f &&& g
val first: Int -> String                = Total.compose(fst[String, Boolean], paired)  // = f, by the product law
val merged: Either[Int, Int] -> String = f ||| (n => (-n).toString)

val curried: Int -> Int -> Int = Total.Exponential.curry[Int, Int, Int]((c, a) => c + a)
```

The equation "uniqueness" becomes a law too: `pairUniqueness` says that every arrow into a product is the pairing of its two projections. When the mediating arrow is given by a program, uniqueness is an equation that can be tested like any other law.

These constructions also satisfy the expected relations. For instance, products distribute over coproducts: `(A, Either[B, C])` ≅ `Either[(A, B), (A, C)]`. **[Proved]**

### 14.3 The collapse theorem, categorically

Section 2.5 promised a categorical form of Theorem 2.4.

**Proposition 14.3.** In a cartesian closed category with an initial object 0: **[Proved]**

1. For every object A, A × 0 ≅ 0.
2. Every arrow f : A → 0 is an isomorphism; that is, 0 is a **strict** initial object.
3. If there is an arrow 1 → 0, then every object is isomorphic to 0, and every hom-set has exactly one element.

*Proof.* (1) Arrows A × 0 → C correspond to arrows 0 → (A ⇒ C) by the exponential property, and there is exactly one of those, so A × 0 has exactly one arrow to every object: it is initial, hence isomorphic to 0. (2) Given f : A → 0, the arrow ⟨id, f⟩ : A → A × 0 has the projection π₁ as a left inverse. In the other direction, ⟨id, f⟩ ∘ π₁ is an arrow out of A × 0, which is initial by (1), so it equals the identity. Hence A ≅ A × 0 ≅ 0. (3) An arrow 1 → 0 makes 1 ≅ 0 by (2). Then for any objects A and B, arrows A → B correspond to arrows A × 1 → B, hence to arrows A × 0 → B, and by (1) there is exactly one of those. ∎

The expression `z: Nothing` of property (D) is exactly an arrow `Unit` → `Nothing`, so Proposition 14.3 is the categorical content of Theorem 2.4. A bicartesian closed category of programs cannot contain a program that does not terminate. That is why 𝒮 is bicartesian closed and 𝒫 is not: in 𝒫, `loop()` is an arrow `Unit` → `Nothing`. 𝒫 keeps its coproducts (`Partial.Coproduct`), but its pairs are not products. In 𝒫, π₁ ∘ ⟨f, g⟩ is f only where g terminates, because pairing runs both. Pairs in 𝒫 form a weaker structure, called a monoidal structure (section 14.5), and chapter 18 shows that they are still products of a precise kind, *restriction products*.

### 14.4 Points and well-pointedness

An arrow 1 → A is called a **point** of A. In 𝒮, points of A correspond to total values of A, so Val is, up to isomorphism, the functor "points of", 𝒮(`Unit`, −). **[Proved]** Definition 2.5 says that two arrows A → B are equal when they agree on every total value of A, that is, on every point. A category with this property is called **well-pointed** **[Standard, from memory]**. Set is well-pointed, and so is 𝒮. Well-pointedness is what lets us reason about arrows of 𝒮 "elementwise", as if they were functions between sets, which is the faithfulness of Val (Proposition 2.10) in categorical dress.

### 14.5 Monoidal structure

Products are one way to combine two objects into one. They are not the only one, and Part IV needs others: the coproduct, which also combines two objects, and the pairs of 𝒫, which combine objects but are not products. What do they have in common? Section 4.2 already gave the answer, in order to define enriched categories: a **monoidal structure**, a bifunctor ⊗ with a unit object I, associative and unital up to coherent isomorphisms (the associator α and the unitors λ and ρ, satisfying the pentagon and triangle equations).

The library has a hierarchy of monoidal structures, each a refinement of the previous one:

| Class | Adds | Instances |
| --- | --- | --- |
| `Monoidal(K, U, T)` | a unit object `I`, given by its evidence `U`, a tensor bifunctor `T`, isomorphisms α, λ, ρ; laws: naturality, pentagon, triangle | — |
| `Symmetric(K, U, T)` | a braiding β : A ⊗ B → B ⊗ A with β ∘ β = id; laws: naturality, symmetry, hexagon | `Partial.Product` |
| `Cartesian(K, U, T)` | the tensor is a product: `fst`, `snd`, `pair` (`&&&`), `discard`; the isomorphisms are derived | `Total.Product` |
| `Cocartesian(K, U, T)` | the tensor is a coproduct: `inl`, `inr`, `copair` (`|||`), `absurd` | `Total.Coproduct`, `Partial.Coproduct` |
| `Closed(M)` | exponentials for a monoidal `M`: `eval`, `curry`, and the internal hom as a profunctor, `internalHom` | `Total.Exponential` |

`Cartesian` and `Cocartesian` are refinements of `Symmetric`, because being a product is a property of a tensor: it says that the tensor of two objects has the universal property of section 14.1. The library therefore derives their associator, unitors and braiding from the projections or injections, and checks one extra law, `tensorIsProduct` (or `tensorIsCoproduct`), that the tensor of arrows is the one the universal property gives. `Closed`, on the other hand, is structure *on* a monoidal category, so it takes one as a parameter.

`Partial.Product` is the example of a monoidal structure that is not cartesian. Its tensor of arrows, from section 12.3, runs both arrows. Its unitors and associator are the obvious reshufflings of tuples, and its laws are **[Tested]** on total programs; for programs that do not terminate they hold by the argument of chapter 18.

### 14.6 Universal constructions in your own categories

A universal property can be stated for any category as a class, and its "exactly one" part becomes an equational law. That is how `Cartesian` and `Cocartesian` work: their laws `fstPair`, `sndPair` and `pairUniqueness` are the universal property of section 14.1, read as equations. To show that your own category has products, extend `Cartesian` with your category and a bifunctor for the tensor, implement `fst`, `snd`, `pair` and `discard`, and run the generic specification of chapter 22.

### 14.7 Joins: coproducts in a preorder

Universal constructions mean something even in a preorder (section 1.2), where there is at most one arrow between two objects. There, an arrow a → b says a ≤ b, and the uniqueness half of a universal property is automatic. What remains is the existence half, and it has a familiar name.

- A **coproduct** of a and b is an object a ∨ b with a ≤ a ∨ b and b ≤ a ∨ b, such that a ≤ x and b ≤ x imply a ∨ b ≤ x. That is the least upper bound of a and b, also called their **join**.
- An **initial object** is a least element, written ⊥.
- A preorder with a least element and a join for every two elements is a **join-semilattice**: a preorder with all finite coproducts.
- A monotone map is a functor between preorders (section 1.4). It preserves joins exactly when it preserves coproducts.

Here is a join-semilattice in code: positions in a text, ordered by ≤, with the larger one as join and −1 as least element.

```scala library
val bottom: Int                   = -1
def join(a: Int, b: Int): Int    = a.max(b)
def below(a: Int, b: Int): Boolean = join(a, b) == b
```

`below(a, b)` holds exactly when a ≤ b, so the order can be recovered from the join. This is the beginning of a structure that chapter 20 needs. A parser reports the furthest position at which something failed, and that report combines with other reports by exactly this join. Chapter 15 shows the same structure from the side of monoids.

### 14.8 What is missing

𝒮 has finite products, finite coproducts, exponentials, a natural numbers object (chapter 16) and initial algebras of many functors. It lacks, uniformly, the constructions that need subsets or quotients: equalizers and pullbacks (chapter 6), coequalizers (chapter 7). It also lacks a **subobject classifier**, an object that classifies all subsets: `Boolean` classifies only the decidable ones. So 𝒮 is not a **topos**, the kind of category that behaves most like Set.

| Construction | Set | 𝒮 | 𝒫 |
| --- | --- | --- | --- |
| terminal, initial | yes | `Unit`, `Nothing` | `Nothing` is initial; `Unit` is not terminal, since `_ => loop()` is a second arrow into it |
| products | yes | tuples | not products; tuples form a symmetric monoidal structure (restriction products, chapter 18) |
| coproducts | yes | `Either` | `Either` |
| exponentials | yes | function types | not in the sense of section 14.1 |
| equalizers, pullbacks | yes | no uniform construction (chapter 6) | — |
| coequalizers | yes | no uniform construction (chapter 7) | — |
| subobject classifier | yes | no; `Boolean` classifies decidable subsets only | no |
| polymorphic types as ends | no counterpart in the same form | yes (chapter 9) | yes |

### 14.9 Set and Scala

In Set, every universal construction exists, and its uniqueness is a theorem about sets. In 𝒮, the finite ones exist, they are programs, and their uniqueness is a law that can be tested. In 𝒫, the constructions that would let a program detect non-termination, products and a terminal object, are lost, which is the categorical shadow of the halting problem. The monoidal structures of the library describe what remains.

### References for chapter 14

**Cited from memory, not consulted**

- Steve Awodey, *Category Theory*, 2010: universal properties, cartesian closed categories, strict initial objects, well-pointedness, toposes, joins as coproducts in a preorder.
- Saunders Mac Lane, *Categories for the Working Mathematician*, 1998: monoidal categories, coherence.

---

## Chapter 15. Monads, monoid objects and adjunctions

### 15.1 The idea

C1 excluded effects from the arrows of 𝒮, but it did not exclude effects from programs. It required them to be visible in types. A **monad** is the standard way to make an effect visible: a type constructor `M` such that a value of `M[A]` is "a computation with some effect that produces an `A`", together with a way to produce a value without effect and a way to sequence computations.

### 15.2 Monads and their Kleisli categories

**Definition 15.1 (monad).** A **monad** on a category 𝒦 is an endofunctor M : 𝒦 → 𝒦 together with arrows η_A : A → M(A), the **unit**, and μ_A : M(M(A)) → M(A), the **multiplication**, both natural in A, such that

- μ ∘ η_M = id (left unit),
- μ ∘ M(η) = id (right unit),
- μ ∘ μ_M = μ ∘ M(μ) (associativity).

The multiplication flattens a computation of a computation. Its most useful consequence is the **extension** of an arrow f : A → M(B), the arrow f\* = μ ∘ M(f) : M(A) → M(B), which runs a computation and continues with f. Unit and extension determine the monad, since M(f) = (η ∘ f)\* and μ = id\*, and in their terms the laws read f\* ∘ η = f, η\* = id and g\* ∘ f\* = (g\* ∘ f)\*. This second presentation is called a **Kleisli triple** **[Standard: Manes 1976, from memory]**.

The library's `Monad(F)` is the first presentation. It takes the endofunctor F as a parameter, because a monad is structure on a functor, and adds `unit` and `flatten`; `bind`, the extension, is derived. On 𝒮 it reads as the familiar interface:

```scala library
import parrot.category.*

val O = Monad.OptionIsMonad

val half: Int -> Option[Int]      = n => if n % 2 == 0 then Some(n / 2) else None
val quarter: Option[Int] -> Option[Int] = O.bind(half) andThen O.bind(half)
```

`O.bind(half)` is what Scala's `flatMap(half)` does, as a function of the computation. Every monad gives a category with the same objects as 𝒦, its **Kleisli category**, whose arrows A → B are arrows A → M(B) of 𝒦, with η as identity and g\* ∘ f as composition. It generalizes `OptionKleisli` of section 3.5. In the library it is `Kleisli(M)`, a promonad (chapter 17), whose category of arrows is `Kleisli(M).category`.

**Proposition 15.2.** The monad laws hold exactly when the Kleisli category laws hold. **[Proved, sketch]** In terms of the extension, the left identity law of the Kleisli category is η\* = id, its right identity law is f\* ∘ η = f, and its associativity is g\* ∘ f\* = (g\* ∘ f)\*. Each follows from the monad laws and the naturality of η and μ, and conversely the three give back the monad laws with M(f) = (η ∘ f)\* and μ = id\*.

So a monad is a way of building a new category of effectful arrows on top of 𝒦. The library has the monads that parsers need, built from three **transformers**, each of which adds one effect to a monad that already exists:

| Monad | `M[A]` | Effect | In the library |
| --- | --- | --- | --- |
| `Option` | `Option[A]` | possible absence of a result | `Monad.OptionIsMonad` |
| Writer | `(W, A)`, with W a monoid | producing output | `Writer(W)` |
| failure transformer | `M[Option[A]]` | failure, on top of the effects of M | `OptionT(M)` |
| state transformer | `S -> M[(A, S)]` | reading and updating a state, with the effects of M | `StateT[S](M)` |

For instance, the reference parser of chapter 20 is the Kleisli category of `StateT[Input](OptionT(Writer(E)))`: it reads and consumes input, reports diagnostics, and may fail. `Either[E, *]`, `List` and the reader monad `R -> A` are monads too, and the tests use `Writer` for strings, whose order of output matters (chapter 17).

The laws also justify the rewriting of `for`-comprehensions. `for { x <- m; y <- f(x) } yield y` is the same computation as `m.flatMap(f)` by the right unit law, and nested comprehensions can be flattened by associativity. These rewrites are sound for every lawful monad and only for lawful ones.

### 15.3 Monoid objects

Section 1.2 defined a monoid as a set with an associative operation and a unit. The definition uses sets, pairs and elements, so it is a definition in Set. Chapter 14 showed what replaces pairs in a general category, a monoidal structure, and that replaces the definition too.

**Definition 15.3 (monoid object).** A **monoid** in a monoidal category (𝒦, ⊗, I) is an object M with arrows η : I → M, the unit, and μ : M ⊗ M → M, the multiplication, such that μ ∘ (η ⊗ id) = λ, μ ∘ (id ⊗ η) = ρ and μ ∘ (μ ⊗ id) = μ ∘ (id ⊗ μ) ∘ α.

In 𝒮 with pairs, η picks out an element and μ is a binary operation, so a monoid object is an ordinary monoid whose operations are programs:

```scala library
object Concatenation extends Monoid(Total.Product):
  type Self = String
  def carrier: String is Type                 = Type.TIsType
  def unit: Unit -> String                    = _ => ""
  def multiply: ((String, String)) -> String = (a, b) => a + b
```

The laws of `Concatenation` are **[Tested]**. In other monoidal categories, monoid objects are other things: in endofunctors with composition as tensor, they are monads (section 15.4).

**Semilattices.** Some monoids have two extra properties: the order of the arguments does not matter, μ ∘ β = μ (**commutativity**), and combining a value with itself changes nothing, μ ∘ Δ = id (**idempotence**). The second law uses the diagonal Δ = ⟨id, id⟩, so it only makes sense when the tensor is a product. A commutative, idempotent monoid in a cartesian category is a **semilattice**, and in the library `Semilattice(M)` refines `Monoid(M)` for a `Cartesian` structure `M`.

Here is the connection with section 14.7. Given a semilattice, define a ≤ b to mean a · b = b. The monoid laws make this a preorder, and in it a · b is the join of a and b and the unit is the least element. Conversely, a join-semilattice gives a semilattice with the join as multiplication and ⊥ as unit. **[Standard: from memory]**

> A join-semilattice is the same thing as a commutative idempotent monoid. In the language of categories, it is a preorder with finite coproducts, and also a monoid object with two extra laws.

Two descriptions of one structure are useful because each makes different things easy. The monoid view says how to combine reports. The preorder view says when one report carries at least the information of another. Chapter 20 uses both. Maps that preserve the structure agree too: a monoid homomorphism between semilattices is a monotone map that preserves joins, a coproduct-preserving functor between the preorders.

Strings under concatenation are a monoid but not a semilattice: `"ab"` is not `"ba"`, and `"aa"` is not `"a"`. The tests record both failures as counterexamples. Positions under `max`, from section 14.7, are a semilattice, as are booleans under `||` and sets under union.

**Comonoids.** Reversing the arrows of Definition 15.3 gives a **comonoid**: an object C with a counit ε : C → I and a comultiplication δ : C → C ⊗ C, satisfying the mirrored laws. A comonoid is something that can be deleted and copied. In a cartesian category every object is a comonoid in exactly one way, with ! and Δ, which the library offers as `Total.Product.comonoid[A]`. This characterizes cartesian categories: a symmetric monoidal category is cartesian exactly when every object has a comonoid structure that every arrow preserves **[Standard: Fox 1976, from memory]**. Pairs in 𝒫 show what the second condition adds. Copying and deleting are total programs, so every type is a comonoid for the pairs of 𝒫 (`Partial.Product.comonoid[A]`), but a program that does not terminate cannot be deleted: running it and discarding its result is not the same as discarding its argument. So the pairs of 𝒫 are not products, as section 14.3 found by another route, and chapter 17 meets the same distinction as effects that can or cannot be copied and discarded. The comonoid laws of both instances are **[Tested]**.

### 15.4 A monad is a monoid in the category of endofunctors

With `Category1` of chapter 10, the slogan becomes a precise comparison. Composition of type constructors, `[A] =>> F[G[A]]`, is a tensor on the category of endofunctors, with the identity type constructor `[A] =>> A` as unit. A monoid for this tensor, in the sense of Definition 15.3, consists of a unit `[A] => A -> M[A]` and a multiplication `[A] => M[M[A]] -> M[A]`, satisfying the unit and associativity laws. These are exactly the laws of Definition 15.1 **[Standard: Mac Lane 1998, from memory]**, which is why the library's `Monad` takes `flatten`, not `bind`, as its primitive. As chapter 10 explained, Scala cannot state "monoid in a monoidal category" once for all kinds, so the library has two classes with the same shape, a carrier, a unit and a multiplication: `Monoid` for objects of kind \* and `Monad` for endofunctors.

### 15.5 Adjunctions

**Definition 15.4 (adjunction).** An **adjunction** between categories 𝒞 and 𝒟 consists of functors F : 𝒞 → 𝒟 and G : 𝒟 → 𝒞 with a bijection

𝒟(F(a), b) ≅ 𝒞(a, G(b))

for all objects a and b, natural in both. F is the **left adjoint** and G the **right adjoint**, written F ⊣ G.

**Currying is an adjunction.** For a fixed type S, the functor `[A] =>> (A, S)` is left adjoint to `[B] =>> S -> B`. The bijection is `Total.Exponential.curry` and its inverse `uncurry`, natural in both arguments, which is the exponential property of section 14.2 again. **[Proved]**

**Every adjunction gives a monad.** If F ⊣ G, then G ∘ F is a monad **[Standard: Mac Lane 1998, from memory]**. For currying, G ∘ F sends A to `S -> (A, S)`, which is the state monad. So State is not an ad hoc invention: it is what the currying adjunction produces. The library's `StateT[S](M)` places the effects of another monad between the two adjoints, `S -> M[(A, S)]`:

```scala library
object Counter extends StateT[Int](Monad.OptionIsMonad)

val tick: Unit -> Int -> Option[(Int, Int)] = _ => n => Some((n, n + 1))
val ticked: Int -> Option[(Int, Int)]       = Counter.bind(tick)(Counter.unit(()))
```

`ticked` runs a step that does nothing, then `tick`, which reads the counter and increments it: started at 3, it returns 3 and leaves 4. The state threads through the composite without being mentioned.

### 15.6 The free monoid, honestly

The list type is the **free monoid**. For every type `A`, every monoid `N` and every function `f: A -> N`, the function `foldMap(f): List[A] -> N` of section 6.8 is a monoid homomorphism, and it is the *only* homomorphism that sends each one-element list `List(a)` to `f(a)`.

**Proposition 15.5.** For every monoid homomorphism `h: List[A] -> N`, h ≐ `foldMap(a => h(List(a)))`. **[Proved]**

*Proof.* By Definition 2.5 it suffices to show that both sides agree on every total list, which follows by induction on the list, a finite tree. On the empty list, h gives the unit of N because h is a homomorphism, and so does foldMap. On `a :: xs`, h gives `h(List(a)) · h(xs)` because h preserves the operation and `a :: xs` is `List(a) ++ xs`, and foldMap gives the same by the induction hypothesis. ∎

In category theory this is an adjunction between Set and the category of monoids: free monoid on the left, "forget the monoid structure" on the right, with the bijection "homomorphisms from the free monoid on A to N" ≅ "functions from A to the carrier of N". In Scala, the category of monoids is not an 𝒮-category, because its homs are subsets (chapter 6). So the adjunction exists as an adjunction of ordinary categories. But the bijection is remarkable for Scala: its right side, `A -> N`, *is* a type, so the subset of homomorphisms out of a free monoid is represented by a type, exactly as section 6.8 said.

### 15.7 What the theory guarantees

A lawful monad gives a lawful Kleisli category, so every theorem about categories applies to effectful arrows: the generic algorithm of section 3.9 runs for any monad, for instance. The rewriting of `for`-comprehensions is sound. And effects are modeled purely: a state computation is a pure function of the state, so C1 is respected.

The guarantee stops where the laws stop. A "monad" whose `bind` breaks associativity, which happens with some effect-tracking types in the wild, gives no category, and refactoring its `for`-comprehensions can change behavior.

### References for chapter 15

**Cited from memory, not consulted**

- Eugenio Moggi, "Notions of computation and monads", *Information and Computation* 93, 1991.
- Saunders Mac Lane, *Categories for the Working Mathematician*, 1998: monads, adjunctions, monoids in monoidal categories, the monad of an adjunction.
- The equivalence of join-semilattices with commutative idempotent monoids.

---

## Chapter 16. Recursion on categories

### 16.1 The idea

Recursive data types such as lists and trees, and the recursive functions that consume them, have a categorical description that explains why structural recursion always terminates and why it is the canonical way to consume data. Programs also recurse in ways that are not structural: they loop until a condition holds, or call themselves until they are done. This chapter treats both, and finds where each lives: folds in 𝒮, general loops and recursion in 𝒫, and, in between, recursion that is total because it makes progress.

**Definition 16.1 (algebra).** For an endofunctor F on a category 𝒞, an **F-algebra** is an object A with an arrow a : F(A) → A. A **homomorphism** from (A, a) to (B, b) is an arrow h : A → B with h ∘ a = b ∘ F(h). An **initial algebra** is an F-algebra (μF, in) from which there is exactly one homomorphism to every other F-algebra. That unique homomorphism is called the **fold**, or **catamorphism**.

Lambek's lemma says that the structure map of an initial algebra is an isomorphism: μF ≅ F(μF) **[Standard: Lambek 1968, from memory]**. So the initial algebra is a fixed point of F, the smallest one.

### 16.2 Folds in 𝒮

A recursive data type is the initial algebra of its **pattern functor**, the functor obtained by replacing the recursive occurrences with a parameter:

```scala library
import parrot.category.*

enum ExprF[R]:
  case Lit(n: BigInt)
  case Add(l: R, r: R)
  case Mul(l: R, r: R)

object ExprFunctor extends Functor(Total, Total):
  type Self[R] = ExprF[R]
  def objects[A: Type]: ExprF[A] is Type = Type.TIsType
  def map[A: Type, B: Type](f: A -> B): ExprF[A] -> ExprF[B] =
    case ExprF.Lit(n)    => ExprF.Lit(n)
    case ExprF.Add(l, r) => ExprF.Add(f(l), f(r))
    case ExprF.Mul(l, r) => ExprF.Mul(f(l), f(r))

final case class Fix[F[_]](unfix: F[Fix[F]])
type Expr = Fix[ExprF]

def fold[A](alg: ExprF[A] -> A)(x: Expr): A =
  alg(ExprFunctor.map[Expr, A](fold(alg))(x.unfix))

val eval: Expr -> BigInt = fold[BigInt] {
  case ExprF.Lit(n)    => n
  case ExprF.Add(l, r) => l + r
  case ExprF.Mul(l, r) => l * r
}
```

`fold(alg)` is the unique homomorphism from the initial algebra `(Fix[ExprF], Fix(_))` to the algebra `(BigInt, alg)`.

**Proposition 16.2.** For a strictly positive pattern functor, `fold(alg)` terminates on every total value, and it is the only function `h` with `h(Fix(e))` ≐ `alg(e.map(h))` for all `e`. **[Proved]**

*Proof sketch.* A total value of `Fix[F]` is a finite tree, because it was built by finitely many constructor applications. `fold` recurses on the immediate subtrees, so it terminates. If `h` satisfies the equation, then h and `fold(alg)` agree on every tree by induction on its height, and Definition 2.5 makes them equal. ∎

The restriction to **strictly positive** functors, in which the recursive parameter never appears to the left of a function arrow, is essential. With `F[R] = R -> Int`, the type `Fix[F]` contains a value that applies itself to itself, and folds over it loop forever **[Standard, from memory]**. Scala does not check strict positivity, so it is a **[Convention]**.

Programmers mostly write folds by hand, as ordinary structural recursion, rather than through `Fix`. The categorical view still explains what they are doing: every structurally recursive function on a data type is a fold, unique once its behavior on each constructor is fixed. That uniqueness is what makes "prove it by induction on the structure" a complete proof method for functions on data.

### 16.3 Beyond folds: recursion with a measure

Not every terminating function is a fold. Merge sort, Euclid's algorithm and many others recurse on arguments that are smaller in some measure but not structurally smaller. Stainless checks such functions by verifying a decreasing measure, specified with `decreases`, or by inferring one **[Stainless README and EuroProofNet wiki, checked]**. Otherwise the programmer promises termination, which in the library means writing the function as an arrow of 𝒮, or as a program of 𝒫 turned into one by `Partial.assumeTotal`.

What no total language can do is define its own interpreter: an interpreter for all total programs of a language, written in that language, would allow a diagonal argument like the one in section 5.3 **[Standard, from memory]**. Number the total programs from naturals to naturals, and suppose a total program `eval(p, n)` ran program number p on n. Then `n => eval(n, n) + 1` would be a total program too, with some number d, and running it on d would give eval(d, d) = eval(d, d) + 1. This is the precise sense in which totality costs expressiveness, and why 𝒮 is defined as the total part of a language that can loop (chapter 2) rather than as a language that cannot.

### 16.4 Loops and recursion in 𝒫

General recursion and unbounded loops produce programs that may not terminate, so they belong to 𝒫. The library has both, as structures on `Partial`.

**Loops.** A step of a loop takes a state and either stops with a result or continues with a new state: an arrow X → A + X. Running it until it stops is an operation from such arrows to arrows X → A, which chapter 19 calls **iteration** and studies in general. In 𝒫 it is the while loop:

```scala library
val gcdStep: (Int, Int) ~> Either[Int, (Int, Int)] =
  Partial.fromTotal((a, b) => if b == 0 then Left(a.abs) else Right((b, a % b)))

val gcd: (Int, Int) ~> Int = Partial.Loops.iterate(gcdStep)
val six: Int                = gcd.run((12, 18))
```

`Partial.Loops.iterate` accepts any step, including one that never stops; that is why it is an operation of 𝒫 and not of 𝒮. Euclid's algorithm does stop, because the second component decreases, and `Partial.assumeTotal(gcd)` would record that promise.

**Recursion.** Section 2.7 explained that a strict language has fixed points at function types: `fix(f)` ties a knot `k = f(a => k(a))`, and the η-expansion delays the recursive reference until the function is applied. In the library, recursion at the types of programs is the structure `Recursion`, and its instance for 𝒫 is `Partial.Knots`:

```scala library
val factorial: BigInt ~> BigInt =
  Partial.Knots.fix[BigInt, BigInt](rec => Partial(n => if n <= 0 then 1 else n * rec.run(n - 1)))
```

Building the knot terminates whenever `f` does. Running it may not: `Partial.Knots.fix[Int, Int](rec => rec)` builds a program that loops on every argument. Its law, `fix(f) = f(fix(f))`, holds in 𝒫, where the program that never terminates is a legitimate value **[Tested, on terminating functions]**.

### 16.5 Why recursion cannot be total in general

Why not have these operations in 𝒮 as well, for every argument? Proposition 14.3 answers it. A category with products, function types, an initial object and a fixed point for every arrow X → X has an arrow 1 → 0, namely the fixed point of the identity on 0, and then it collapses. 𝒮 has products, function types and an initial object, so it cannot have a fixed-point operator defined on all arrows. This is one instance of a family of theorems: categories with function types in which every endomorphism has a fixed point collapse as soon as they also have coproducts or an initial object **[Standard: Huwig and Poigné 1990, checked (bibliographic entry and a survey's statement of the theorem)]**.

So the library splits recursion in two:

- **unguarded** recursion and iteration, defined for every argument, in 𝒫 (`Partial.Loops`, `Partial.Knots`);
- **guarded** recursion and iteration, defined for every argument and total, but correct only for arguments that make progress, in 𝒮.

### 16.6 Guardedness: recursion that makes progress

A recognizer for balanced parentheses calls itself, but only after it has consumed an opening parenthesis. Every recursive call therefore sees a shorter input, and since lengths cannot decrease forever, the recognizer terminates on every input. The same argument works for any recursion whose calls come after progress in some measure that cannot decrease forever. Such recursion is called **guarded**.

The library makes the argument into a construction. A recognizer reads a remaining input and may fail, so it is a Kleisli arrow of the state monad over `Option` (chapter 15), with strings as states. A `Measure` says how big a state is. `StateT.GuardedRecursion` then ties a knot that is total: a recursive call fails, instead of recursing, unless the measure has decreased since the enclosing call began.

```scala library
given StringIsMeasure: String is Measure:
  def measure(s: String): Int = s.length

object Remaining  extends StateT[String](Monad.OptionIsMonad)
object Recognizer extends Kleisli(Remaining)
object Guarded    extends StateT.GuardedRecursion(Recognizer, ClassicalMonad.OptionIsClassical)

type R = Unit -> String -> Option[(Unit, String)]

def char(c: Char): R      = _ => s => if s.headOption.contains(c) then Some(((), s.tail)) else None
def seq(p: R, q: R): R    = Recognizer.multiply(q, p)
def alt(p: R, q: R): R    = u => s => p(u)(s).orElse(q(u)(s))
val empty: R              = Recognizer.identity[Unit]

// balanced ::= "(" balanced ")" balanced | ε
val balanced: R = Guarded.fix[Unit, Unit](rec => alt(seq(char('('), seq(rec, seq(char(')'), rec))), empty))

val accepted: Option[(Unit, String)] = balanced(())("(()())")
```

`balanced` runs on every input and stops: each recursive call follows a parenthesis. A grammar that calls itself *first*, as in `rec => alt(seq(rec, char('(')), empty)`, is **left-recursive**: its first call happens at the same position as the enclosing one. Under `GuardedRecursion` that call fails, and only the other alternative remains; under `Partial.Knots` it would loop forever. Chapter 19 states the laws: the guarded fixed point satisfies `fix(f) = f(fix(f))` exactly when `f` is guarded, and the tests exhibit a left-recursive `f` for which it does not **[Tested]**. Guarded iteration works the same way: a loop step that continues without decreasing the measure fails.

Guardedness is a semantic property. Nothing checks that a function is guarded before it runs. What the construction guarantees is weaker and still useful: the result is always total, and it is the intended fixed point whenever the function is guarded.

### 16.7 Codata and laziness

The dual of an initial algebra is a **final coalgebra**: an object with an arrow ν F → F(ν F) to which every other coalgebra maps uniquely, by an **unfold**. Final coalgebras describe infinite structures, such as infinite streams, which Scala represents with `LazyList`. Functions that produce them must be **productive**, producing each next piece after finitely many steps, rather than terminating. Section 2.7 placed infinite structures outside the model of this document. A treatment of codata under the contract would need a notion of totality that includes productivity, and of observational equality for infinite structures, which is usually given by bisimulation **[Standard, from memory]**. Productivity is itself a guardedness condition, on producing rather than on consuming. It is not developed here **[Open]**.

### 16.8 Set and Scala

In Set, every polynomial functor has an initial algebra, induction is valid, and every function between sets exists, whether or not a program computes it. In 𝒮, the same holds for strictly positive pattern functors: data are finite trees, folds terminate and are unique, and induction proves equations between functions on data. General recursion is the price Set does not pay: in 𝒮 it collapses the category, so it lives in 𝒫, and in 𝒮 only recursion that makes progress remains.

### References for chapter 16

**Consulted while writing this chapter**

- Stainless repository README. https://github.com/epfl-lara/stainless
- EuroProofNet wiki, "Stainless". https://github.com/EuroProofNet/ProgramVerification/wiki/Stainless

**Cited from memory, not consulted**

- Joachim Lambek, "A fixpoint theorem for complete categories", *Mathematische Zeitschrift* 103, 1968.
- Erik Meijer, Maarten Fokkinga and Ross Paterson, "Functional programming with bananas, lenses, envelopes and barbed wire", *FPCA 1991*.
- The failure of termination for non-strictly-positive recursive types; final coalgebras and bisimulation.

---

# Part IV. Effects as structure

Part III built categories of effectful arrows from monads. This part looks at effectful arrows directly, as categories built on top of 𝒮 with extra structure: running arrows side by side, failing and recovering, looping and recursing. Each structure is introduced by the problem it solves, and the last chapter puts them together into a parser library, whose combinators are exactly these structures.

## Chapter 17. Promonads and Freyd categories

### 17.1 The idea

There are two common ways to represent effectful arrows in Scala.

- **As functions with an effectful result**: `A -> Option[B]`, `A -> (W, B)`, `A -> S -> Option[(B, S)]`. These are the Kleisli categories of chapter 15.
- **As data**: a syntax tree that describes what an arrow does, interpreted later. The optimizing parser of chapter 20 represents a parser as a tree of nodes, `Literal("a")`, `Seq(p, q)`, `Choice(...)`, so that it can analyze and rewrite the tree before running it.

Both kinds have the same two operations. They contain the pure functions: a function `f: A -> B` is an arrow that does nothing but apply f, `a => Some(f(a))` in the first case, a node `Pure(f)` in the second. And they compose. A data representation is not a Kleisli category of any monad (there is no `M[B]` whose values are syntax trees from A), so what structure do the two share? The answer is a category that sits on top of a category 𝒦 of pure functions, together with a way to include 𝒦 in it.

### 17.2 Promonads

**Definition 17.1 (promonad).** A **promonad** on a category 𝒦 is a profunctor P on 𝒦 (Definition 12.2), valued in 𝒮, with

- a **unit**, an arrow 𝒦(A, B) → P(A, B) for all A and B, which includes the pure arrows, and
- a **multiplication**, an arrow P(B, C) × P(A, B) → P(A, C), which composes,

such that the multiplication is associative and has the units of identities as identities, and the unit preserves composition.

A promonad is a monoid in the category of profunctors on 𝒦, in the sense of Definition 15.3, with composition of profunctors as tensor **[Standard: from memory]**. That is why it is called a *pro*monad. Equivalently, and more concretely, a promonad is a category with the same objects as 𝒦 together with a functor from 𝒦 into it that is the identity on objects: its arrows A → B are the elements of P(A, B), its composition is the multiplication, and the functor is the unit **[Standard: from memory]**. The profunctor action of P is then determined: pre- and post-composing with pure arrows is multiplying by their units.

The library's `Promonad(K)` has `unit` and `multiply`, the composition `andThen` in diagrammatic and `compose` in mathematical order, written infix `>>>` and `<<<` as in a category, and `category`, the category of its arrows. Its laws are the category laws of `category` and the functor laws of `unit`, **[Tested]** for every instance.

```scala library
import parrot.category.*
import Kleisli.OptionKleisli.>>>

val parse: String -> Option[Int]  = _.toIntOption
val positive: Int -> Option[Int]  = n => Option.when(n > 0)(n)
val pure: Int -> Option[Int]      = Kleisli.OptionKleisli.unit[Int, Int](_ * 2)

val parsePositiveTwice: String -> Option[Int] = parse >>> positive >>> pure
```

The example imports only the Kleisli `>>>`: its arrows are also functions, and with `Total.>>>` in scope as well, `parse >>> positive` would be ambiguous (section 11.4).

Three kinds of promonad appear in this document.

| Promonad | P(A, B) | Example |
| --- | --- | --- |
| the hom promonad of 𝒦 | 𝒦(A, B) itself | `Total.Functions`, `Partial.Programs` |
| the Kleisli promonad of a monad M on 𝒦 | 𝒦(A, M(B)) | `Kleisli(M)`, such as `Kleisli.OptionKleisli` |
| a representation as data | syntax trees from A to B | the nodes of the optimizing parser, over reified pure functions (chapter 20) |

### 17.3 Running arrows side by side: strength

Pure functions can be run side by side on pairs: given f : A → B and g : C → D, the tensor f × g : (A, C) → (B, D) applies f on the left and g on the right (chapter 14). Effectful arrows need the same: a parser for a key and a parser for a value give a parser for a pair. But a promonad alone cannot do it. Its arrows compose; nothing lets an arrow A → B act on a pair whose other component it does not know.

The missing ingredient is the ability to carry a value along unchanged while an arrow runs. The value need not be an object of 𝒦 itself: it is enough that a monoidal category acts on 𝒦, so that a context C and an object A combine into an object C ⊘ A. A **left module** over a monoidal category (ℳ, ⊗, I), also called a left **actegory**, is a category 𝒦 with a bifunctor ⊘ : ℳ × 𝒦 → 𝒦, the **action**, and natural isomorphisms λ : I ⊘ A ≅ A and α : (X ⊗ Y) ⊘ A ≅ X ⊘ (Y ⊘ A) that satisfy the triangle and the pentagon of section 14.5. Every monoidal category is a left module over itself, with ⊘ = ⊗. In the library, a left module is a `Module`, and the self-action is `Module.OfMonoidal`.

**Definition 17.2 (strength).** A **strength** on a profunctor P : 𝒦₁ᵒᵖ × 𝒦₂ → 𝒮, over left modules ⊘₁ on 𝒦₁ and ⊘₂ on 𝒦₂ of the same monoidal category ℳ, is an operation

τ : P(A, B) → P(C ⊘₁ A, C ⊘₂ B),

natural in A and B, dinatural in C, and compatible with the unitors and the associators of the actions.

The laws say that τ commutes with pre- and post-composition (naturality), that it does not depend on how C is presented (dinaturality), that carrying the unit along does nothing (unitality), and that carrying C ⊗ D along is carrying D, then C (associativity). A profunctor with a strength is also called a **Tambara module** **[Standard: Pastro and Street, from memory]**. Because the context sits on the left, τ is a **left strength**, as is the strength X × M(A) → M(X × A) of a monad **[Standard: Moggi 1991, from memory]**.

When ℳ is symmetric and acts on itself, the context can also be carried on the right. The **right strength** τ′ : P(A, B) → P(A ⊗ C, B ⊗ C) comes from the left one by braiding, τ′(p) = P(β, β)(τ(p)), and the two strengths commute: τ′(τ(p)) = P(α, α⁻¹)(τ(τ′(p))). A profunctor with a left and a right strength that commute is **bistrong**. This needs the action to be ⊗ itself: a left module only has C ⊘ A, and nothing of the form A ⊘ C.

The library's `Strong(P, L1, L2)` takes the profunctor and the two modules, and its operation `left` is τ. `Strong.Bistrong(P, M)` takes a symmetric monoidal structure acting on itself and adds `right`, τ′, which is P(β, β) ∘ τ unless an instance overrides it with something more direct. The same class covers two very different strengths.

- **Over products**, τ′ runs an arrow on the left component of a pair and τ on the right one. For a Kleisli promonad on 𝒮, every monad has one: `left(p)((c, a))` runs `p(a)` and pairs `c` with its result (`Kleisli.ProductStrength`).
- **Over coproducts**, τ′ runs an arrow on the left case of an `Either` and passes the right case through untouched, and τ the other way round (`Kleisli.CoproductStrength`). Functional programmers call this structure **choice**. Their `left` is τ′: it names the case of the sum that an arrow runs on, not the side of the action.

The laws of both, for every Kleisli instance in the library, are **[Tested]**.

### 17.4 Freyd categories

A bistrong promonad is almost a structure for running arrows side by side. Name the two strengths after the component an arrow runs on, `first` for τ′ and `second` for τ, and define `p ** q` as `first(p)` followed by `second(q)`. One more condition is needed, that the pure arrows and the composition of the promonad agree with the strength.

**Definition 17.3 (Freyd category).** A **Freyd category** is a promonad P on a symmetric monoidal category 𝒦, bistrong over its tensor, such that

- first(unit(f)) = unit(f ⊗ id): the strength of a pure arrow is the pure tensor, and
- first(q ∘ p) = first(q) ∘ first(p): the strength respects composition.

Freyd categories were introduced to model call-by-value languages with effects **[Standard: Power and Robinson; Levy, Power and Thielecke, from memory]**, and they are the semantics of Haskell's *arrows*, which programmers know as a design pattern **[Standard: Hughes 2000; Jacobs, Heunen and Hasuo 2009, from memory]**. A strong promonad is in fact a monoid in the category of strong profunctors, so the definition is a single monoid once more **[Standard: Rivas and Jaskelioff, from memory]**.

In the library, a Freyd category is not a new structure but the combination of two: the bundle `Freyd(S)` takes a bistrong `S` whose profunctor is a promonad, names its strengths `first` and `second`, states the two laws and offers the parallel composition `parallel`, written `**`.

```scala library
val OptionFreyd = Freyd(Kleisli.OptionProduct)
import OptionFreyd.**

val both: ((String, Int)) -> Option[(Int, Int)] = parse ** positive
```

**Premonoidal, not monoidal.** For pure functions, it does not matter whether the left or the right component is processed first: f ⊗ g = (f ⊗ id) then (id ⊗ g) = (id ⊗ g) then (f ⊗ id). This is the **interchange** law, and it says that ⊗ is a bifunctor. For effectful arrows it can fail, because the two orders run the effects in different orders. A logger whose log is a string shows it: if p logs `"a"` and q logs `"b"`, then `first(p)` followed by `second(q)` logs `"ab"`, and `second(q)` followed by `first(p)` logs `"ba"`. A category with a tensor that is a bifunctor only in each argument separately is called **premonoidal**, and Freyd categories are premonoidal **[Standard: Power and Robinson, from memory]**. The library's tests record the failure of interchange as a counterexample, for the string logger and for parsers, which consume input in order **[Tested: counterexample]**.

What does survive is interchange with *pure* arrows. A pure arrow has no effect to order, so it commutes with every arrow. Arrows with this property are called **central**, and the law `centrality` checks that the pure arrows of a Freyd category are central **[Tested]**.

### 17.5 Writer effects: when effects commute or can be copied

The logger is an instance of a general construction, and a small amount of algebra says exactly when its effects behave well. The **writer** monad of a monoid W (chapter 15) pairs a result with an output, `A -> (W, B)`, and combines outputs with the monoid's operation, in order. Two properties of W translate into two properties of the effects.

- **Commutative effects.** `first(p)` then `second(q)` outputs w_p · w_q; the other order outputs w_q · w_p. So interchange holds for all p and q exactly when W is **commutative**, and then the writer's Kleisli category is monoidal, not just premonoidal **[Proved]**. Option failure is commutative in the same sense: a pair of arrows fails if either does, in either order.
- **Copyable effects.** Running an arrow twice outputs w · w, running it once outputs w. These agree for every w exactly when W is **idempotent**. An arrow whose effect can be performed twice with the same result as once is called **copyable** **[Standard: Führmann, from memory]**. Failure is copyable too: if an arrow fails, it fails both times.

A writer whose monoid is both commutative and idempotent, that is, a **semilattice** (section 15.3), has effects that commute and can be copied. Consuming input, the effect of a parser, has neither property: a parser that consumes `"a"` twice consumes `"aa"`. Chapter 18 shows what these properties mean for testing whether an arrow succeeds, and why backtracking needs outputs that can be repeated without effect. Chapter 20 builds parser diagnostics as a writer whose monoid is a semilattice.

### 17.6 What the theory guarantees

Any construction written once for a Freyd category, such as running two parsers side by side, is correct for every lawful instance: Kleisli arrows of any monad, parsers, and representations as data. Refactorings that move a pure function across an effectful arrow are sound, because pure arrows are central. Refactorings that swap two effectful arrows are sound only when their effects commute, which the theory makes checkable: for a writer, it is commutativity of the monoid.

### 17.7 Set and Scala

In Set, there is only one way to run two functions side by side, and the order never matters. Effects change this. The categorical structure that remains, a promonad with a strength, is still small: two operations and a handful of laws, and it describes Kleisli arrows and syntax trees alike. What it does not promise is an order-independent tensor, which is exactly the information a programmer must keep in mind when effects are involved.

### References for chapter 17

**Cited from memory, not consulted**

- John Power and Edmund Robinson, "Premonoidal categories and notions of computation", *Mathematical Structures in Computer Science* 7, 1997.
- Paul Blain Levy, John Power and Hayo Thielecke, "Modelling environments in call-by-value programming languages", *Information and Computation* 185, 2003.
- John Hughes, "Generalising monads to arrows", *Science of Computer Programming* 37, 2000.
- Bart Jacobs, Chris Heunen and Ichiro Hasuo, "Categorical semantics for arrows", *Journal of Functional Programming* 19, 2009.
- Exequiel Rivas and Mauro Jaskelioff, "Notions of computation as monoids", *Journal of Functional Programming* 27, 2017.
- Craig Pastro and Ross Street, "Doubles for monoidal categories", *Theory and Applications of Categories* 21, 2008 (Tambara modules).
- Carsten Führmann, "Varieties of effects", *FoSSaCS 2002* (copyable and discardable computations).

---

## Chapter 18. Partiality: restriction categories

### 18.1 The idea

Scala programs can be partial in two very different ways.

- A program of 𝒫 may not terminate. No program can detect this (Proposition 2.1), so a program that uses it simply does not terminate either.
- An arrow `A -> Option[B]` of the Kleisli category of `Option` may fail. Failure is a value, `None`, that the next arrow can inspect and recover from.

Both kinds of arrow have a **domain of definition**: the arguments on which they produce a result. In set theory, a domain is a subset, and chapter 6 explained why subsets are not available in 𝒮. This chapter describes domains inside the category, as arrows, which is possible in both cases, and then asks what can be *done* with a domain: test it, complement it, choose an alternative outside it. The answers differ sharply between 𝒫 and `Option`, and they are exactly the operations a parser needs.

### 18.2 Restriction categories

The domain of an arrow f : A → B can be represented by an arrow from A to A: the identity on the arguments where f is defined, undefined elsewhere. It is written f̄ and called the **restriction** of f.

**Definition 18.1 (restriction category).** A **restriction category** is a category in which every arrow f : A → B has a restriction f̄ : A → A, such that (writing composition in diagrammatic order, ⨾, to match code):

- **R1** f̄ ⨾ f = f: restricting f to its own domain changes nothing;
- **R2** f̄ ⨾ ḡ = ḡ ⨾ f̄: restrictions commute;
- **R3** (f̄ ⨾ g)‾ = f̄ ⨾ ḡ: the domain of g restricted to f's domain is the intersection of the domains;
- **R4** f ⨾ ḡ = (f ⨾ g)‾ ⨾ f: testing g after f is testing "f then g" before f.

An arrow is **total** when f̄ = id **[Standard: Cockett and Lack 2002, checked (bibliographic entry)]**.

The axioms are those of Cockett and Lack, who showed that every category of partial maps is a restriction category and characterized which restriction categories arise that way. Two examples:

- **𝒫.** The restriction of a program `p` runs it for its termination only: `a => { p(a); a }`. The total arrows of 𝒫 are exactly the arrows of 𝒮, which is the precise sense of "𝒮 is the total part of 𝒫" **[Standard: Cockett and Lack 2002, from memory; the instance is `Partial.Domains`]**.
- **The Kleisli category of `Option`.** The restriction of `f: A -> Option[B]` is `a => f(a).map(_ => a)`: it succeeds, with its argument, exactly where f succeeds (`Kleisli.OptionDomains`).

```scala library
import parrot.category.*

val half: Int -> Option[Int]        = n => Option.when(n % 2 == 0)(n / 2)
val halfDomain: Int -> Option[Int]  = Kleisli.OptionDomains.restrict(half)    // Some(n) for even n, None otherwise
```

The laws R1 to R4, and the law that pure arrows are total, are **[Tested]** for both instances, and for the parsers of chapter 20. In 𝒫 the tests can only observe terminating programs; for the others the laws follow from the definition by the same calculation.

### 18.3 Restriction products

Section 2.5 noted that pairs misbehave in the presence of divergence: `(1, loop())._1` never returns 1, although taking the first component of a pair should give back what was put there. Restriction categories say exactly how they misbehave. In 𝒫, pairing two programs runs both, so

π₁ ∘ ⟨f, g⟩ = f ∘ ḡ:

the first component of a pair is f, restricted to where g is defined. This is the defining equation of a **restriction product**, the form products take in a restriction category **[Standard: Cockett and Lack, Restriction categories III, from memory]**. Pairs in 𝒫 are not products (section 14.3), but they are restriction products, and with that weaker law, the reasoning about tuples that chapter 14 did in 𝒮 transfers to 𝒫 with explicit restrictions.

The library does not state restriction products as a class; `Partial.Product` is the symmetric monoidal structure underneath them. Nothing in the library needs more, so they are not implemented.

### 18.4 Decisions: classical restriction categories

A restriction tells *where* an arrow is defined, but not what to do outside its domain. Three further operations ask for more.

- A **restriction zero**: an arrow 0 : A → B defined nowhere, with 0̄ = 0, and 0 ⨾ f = 0 = f ⨾ 0.
- A **complement** of a domain: an arrow f̄ᶜ : A → A, defined exactly where f is *not*.
- A **join** of two arrows that agree where both are defined: an arrow defined on the union of their domains.

A restriction category with all three, satisfying their natural laws, is called **classical** **[Standard: Cockett and Manes 2009, checked]**. The two examples part ways here.

- The Kleisli category of `Option` is classical. Its zero is `_ => None`, the complement of f's domain is `a => if f(a).isEmpty then Some(a) else None`, and a join tries one arrow and, where it fails, the other.
- 𝒫 is not. The complement of a program's domain would be a program that terminates exactly where the original does not. Running it would decide the halting problem (Proposition 2.1).

So the difference between the two ways of being partial is not the partiality but the **decidability** of the domain. Failure that can be observed can be complemented; non-termination cannot.

### 18.5 Ordered choice is override

The most useful operation on partial arrows for programmers is not the join but **ordered choice**: run f, and where it fails, run g. Every parser library has it. Is it a join? Only when f and g agree where both are defined; in general, ordered choice prefers f. Lemay and Nester recently gave this operation its own axioms, under the name **override** **[Standard: Lemay and Nester 2026, checked]**:

f ⊳ g = "f where f is defined, g elsewhere".

**Definition 18.2 (override).** An **override** operator on a restriction category satisfies, in diagrammatic order:

- **⊳.1** (f ⊳ g) ⊳ h = f ⊳ (g ⊳ h)
- **⊳.2** f ⊳ (f̄ ⨾ g) = f
- **⊳.3** (ḡ ⨾ f) ⊳ f = f
- **⊳.4** h ⨾ (f ⊳ g) = (h ⨾ f) ⊳ (h ⨾ g)
- **⊳.5** (f ⊳ g)‾ ⨾ h = (f̄ ⨾ h) ⊳ (ḡ ⨾ h)

Their results that matter here: in a classical restriction category the override operator exists and is unique, and it is the join of f with g restricted to the complement of f's domain, f ⊳ g = f ∨ (f̄ᶜ ⨾ g) (their Theorem 43); a restriction zero is a unit for it, 0 ⊳ f = f = f ⊳ 0 (Lemma 36); and on arrows that agree where both are defined, override *is* the join (Theorem 15).

So PEG's ordered choice, the `|>` of chapter 20, is not an ad hoc operator: it is the unique override of a classical restriction category. The library's `Classical` structure has `zero`, `complement` and `orElse` (infix `|>`) with the laws above, and two laws about complements: f̄ ⨾ f̄ᶜ = 0 (a domain and its complement are disjoint) and f̄ ⊳ f̄ᶜ = id (together they cover everything). All are **[Tested]** for the Kleisli category of `Option` and for its state transformer, and for parsers with the qualifications of section 18.7.

```scala library
import Kleisli.OptionDomains.{|>, complement, zero}

val odd: Int -> Option[Int]     = n => Option.when(n % 2 != 0)(n)
val choice: Int -> Option[Int]  = half |> odd           // half where n is even, odd elsewhere
val notEven: Int -> Option[Int] = complement(half)       // Some(n) exactly for odd n
val never: Int -> Option[Int]   = zero[Int, Int]
```

**Why ⊳ distributes on one side only.** Axiom ⊳.4 says that *pre*composition distributes over choice: running h first and then choosing is choosing between "h then f" and "h then g". The mirror equation, (f ⊳ g) ⨾ h = (f ⨾ h) ⊳ (g ⨾ h), is false. Where f is defined, the left side commits to f; if h then fails, the whole fails, while the right side would have tried g ⨾ h. The tests record this as a counterexample for every classical instance **[Tested: counterexample]**. For parsers it is the familiar fact that a PEG alternative cannot be "un-committed" by what follows it.

### 18.6 Attempt

With coproducts, ordered choice has a single-pass form that is easier to implement efficiently. Instead of choosing between two arrows, **attempt** a single arrow and report the outcome:

attempt(p) = (p ⨾ ι₁) ⊳ ι₂ : A → B + A.

`attempt(p)` never fails: it returns p's result on the left where p is defined, and its untouched argument on the right where it is not. Ordered choice and complement are recovered from it with a copairing: p ⊳ q = attempt(p) ⨾ [id, q] and p̄ᶜ = attempt(p) ⨾ [0, id]. The library defines `attempt` from `orElse` by the equation above (law `attemptDefinition`), and interpreters that can do better override it: the optimizing parser of chapter 20 runs `p` once and branches on the result.

### 18.7 Restriction and effects

Chapter 17 asked when effects commute and when they can be copied. Restriction is where the answers matter. Suppose arrows have an effect besides failure, such as producing output: the arrows `A -> (W, Option[B])` of the failure transformer over a writer (chapter 15). What should the restriction f̄ do with f's output?

- **Keep it.** R1 says f̄ ⨾ f = f: the test followed by f must produce f's output once, so the output must be copyable (section 17.5). For a writer whose monoid is a semilattice, R1, R3 and R4 then hold **[Tested]**. R2 does not, whatever the monoid. If f fails and g succeeds, f̄ ⨾ ḡ stops after the test of f and outputs only what f does, while ḡ ⨾ f̄ outputs what both do: failure does not commute with output **[Tested: counterexample]**. The complement laws fail too, because f̄ ⨾ f̄ᶜ always fails, like the zero, but outputs what f does, while the zero outputs nothing **[Tested: counterexample]**. In the library this structure is `OptionT.ClassicalOf`.
- **Drop it.** The restriction is **silent**: f̄ tests f and outputs nothing. R2 and R3 then hold exactly, since silent tests output nothing in either order, and so do the complement laws. R1 and R4 hold only up to the output: where f fails, f̄ ⨾ f fails silently, while f alone outputs something.

In both cases f ⨾ 0 = 0 holds only up to the output, since f produces its output before the failure; no choice of restriction can change that. Otherwise silent tests lose less: two equations hold up to output, where keeping the output breaks R2 and the complement laws outright. Chapter 20 makes this choice for parser diagnostics, and states the equations that hold up to output as inequations: both sides agree on results, and one side outputs at least what the other does.

One requirement on the output remains, whichever restriction is chosen, and it comes from ordered choice. By ⊳.4, h ⨾ (f ⊳ g) = (h ⨾ f) ⊳ (h ⨾ g), and the right side runs h twice where f fails. For a writer, the two sides then produce the same output only if x · y · x = x · y for all outputs x and y; in particular x · x = x **[Proved]**. A semilattice satisfies this and strings do not, and the tests confirm both **[Tested]**. A writer that coexists with backtracking needs a monoid in which repeating an earlier output adds nothing, and a semilattice is the natural one.

### 18.8 What the theory guarantees

For a lawful classical restriction category: lookahead (restriction) can be moved, combined and dropped as R1 to R4 allow; ordered choice is associative, has failure as its unit, and distributes over what comes before it; a domain and its complement exclude each other and cover everything. The guarantee stops at the other side: choice does not distribute over what comes after it, and no law lets an alternative be un-committed.

### 18.9 Set and Scala

In the category of sets and partial functions, every restriction category operation exists: domains, complements, joins, override. In Scala, partiality comes in two kinds. 𝒫's non-termination gives a restriction category whose total part is 𝒮, but complements would decide halting, so it is not classical. `Option`'s failure gives a classical restriction category, and with it ordered choice as a theorem rather than an invention. With effects besides failure, no restriction keeps every law exact: failure does not commute with output, so the tests either lose the output or break the laws of commuting tests and complements.

### References for chapter 18

**Consulted while writing this chapter**

- Jean-Simon Pacaud Lemay and Chad Nester, "Override and Update in Restriction Categories", 2026. https://arxiv.org/abs/2609.03472
- J. R. B. Cockett and E. G. Manes, "Boolean and classical restriction categories", *Mathematical Structures in Computer Science* 19(2), 2009. https://www.cambridge.org/core/journals/mathematical-structures-in-computer-science/article/boolean-and-classical-restriction-categories/DD17198A664E39FC63B543EA5AA7E395 (abstract)

**Cited from memory, not consulted**

- J. R. B. Cockett and S. Lack, "Restriction categories I: categories of partial maps", *Theoretical Computer Science* 270, 2002; "Restriction categories III: colimits, partial limits and extensivity", *Mathematical Structures in Computer Science* 17, 2007.

---

## Chapter 19. Iteration and recursion on promonads

### 19.1 The idea

Chapter 16 found loops and recursion in two places: unguarded in 𝒫 (`Partial.Loops`, `Partial.Knots`), and guarded for recognizers that consume input (`StateT.GuardedRecursion`). Both were presented as operations on particular categories. This chapter asks what they have in common, so that a parser library can state "a grammar may loop and recurse" once, as structure, and every interpreter can supply it in its own way.

There turn out to be three related structures, and each comes in two versions, one for products and one for coproducts. They form a grid:

|  | run beside a context | feed an output back | solve for a fixed point |
| --- | --- | --- | --- |
| **products ×** | strength (chapter 17) | trace: a value defined in terms of itself | Conway operator: recursion |
| **coproducts +** | strength, "choice" (chapter 17) | trace: a loop with an entry and an exit | Elgot operator: iteration |

The first column is chapter 17. This chapter introduces the other two, shows how the columns translate into each other, and explains why, in a strict language, the product row is nearly empty while the coproduct row is full.

### 19.2 Feedback: traces

Think of an arrow p : A ⊗ U → B ⊗ U as a box with two inputs and two outputs. **Feedback** connects the U output back to the U input, and leaves a box from A to B.

**Definition 19.1 (trace).** A **trace** on a promonad P with a strength over a symmetric monoidal structure ⊗ is an operation

tr : P(A ⊗ U, B ⊗ U) → P(A, B)

satisfying, in diagrammatic order (each law is a picture of wires that can be deformed without changing the box):

- **tightening**: tr(first(f) ⨾ p ⨾ first(g)) = f ⨾ tr(p) ⨾ g: what happens before and after the loop can be moved out of it;
- **sliding**: tr(p ⨾ (id ⊗ h)) = tr((id ⊗ h) ⨾ p) for pure h : U → V: a pure transformation on the feedback wire can slide around the loop;
- **vanishing**: tracing out the unit I does nothing, and tracing out U ⊗ V is tracing out V, then U;
- **superposing**: tr(α ⨾ (g ⊗ p) ⨾ α⁻¹) = g ⊗ tr(p) for pure g: a wire that does not take part in the loop can be drawn beside it;
- **yanking**: tr(β) = id: feeding one strand of a braid back into the other gives a straight wire.

**[Standard: Joyal, Street and Verity 1996, from memory]** introduced traced monoidal categories. With effects, the tensor is only premonoidal (section 17.4), and sliding and superposing are restricted to pure arrows, which are central **[Standard: Benton and Hyland 2003, from memory]**. That is the version the library's `Traced(S)` states.

What feedback *means* depends on the tensor.

- With **coproducts**, a value enters on A, and p either exits on B or continues on U. Feeding U back means running p again: tr(p) is a **loop** with an entry and an exit.
- With **products**, p receives an a and a u and returns a b and a new u. Feeding u back means finding a u that p returns unchanged: tr(p) is a **recursive definition** u = p(a, u)₂.

In 𝒫, the loop exists for every p:

```scala library
import parrot.category.*

// 1 + 2 + … + n: enter with n, loop on (i, sum), exit with the sum
val sumStep: Either[Int, (Int, Int)] -> Either[Int, (Int, Int)] = {
  case Left(n)          => Right((n, 0))
  case Right((0, sum))  => Left(sum)
  case Right((i, sum))  => Right((i - 1, sum + i))
}

val sumTo: Int ~> Int = Partial.Feedback.trace[Int, Int, (Int, Int)](Partial.fromTotal(sumStep))
val fiftyFive: Int    = sumTo.run(10)
```

The trace laws for `Partial.Feedback` are **[Tested]**, on loops that terminate.

### 19.3 Iteration: Elgot operators

A loop has an entry and an exit, but most loops do not need a separate entry: the state they start with is the state they continue with. That gives a simpler operation.

**Definition 19.2 (Elgot operator).** An **iteration operator** on a promonad P with a strength over coproducts sends a step p : X → A + X to an arrow p† : X → A, such that

- **fixed point**: p† = p ⨾ [id, p†]: run the step; on A stop, on X continue;
- **naturality**: (p ⨾ (h + id))† = p† ⨾ h for pure h: post-processing the result can be done inside or after the loop;
- **dinaturality**: for f : X → A + Y and g : Y → A + X, (f ⨾ [ι₁, g])† = f ⨾ [id, (g ⨾ [ι₁, f])†]: a loop that alternates two steps can start with either. Its special case for a pure g, (g ⨾ p)† = g ⨾ (p ⨾ (id + g))†, is called `composition` in the library: a pure step at the start of each round can be rotated to the end;
- **codiagonal**, called `doubleDagger`: (p†)† = (p ⨾ [id, ι₂])†: a loop inside a loop with the same state is one loop;
- **uniformity**: if f ⨾ (id + h) = h ⨾ g for pure h, then f† = h ⨾ g†: loops related by a change of state representation h compute the same thing.

An operator with these laws is a **Conway iteration operator**, and Elgot, Bloom and Ésik developed their theory **[Standard: Elgot 1975; Bloom and Ésik 1993, from memory]**. Monads whose Kleisli categories have one are **Elgot monads** **[Standard: Adámek, Milius and Velebil 2011, from memory]**. The library's `Elgot(S)` states the laws, and `Partial.Loops` is the while loop of chapter 16.

Each law is a refactoring of loops.

| Law | Refactoring |
| --- | --- |
| fixed point | unroll one iteration |
| naturality | move post-processing of the result into or out of the loop |
| dinaturality | rotate a loop: start an alternation of two steps with the other one, or move a pure step from the start of the body to the end |
| codiagonal | flatten nested loops over the same state into one |
| uniformity | change the representation of the loop state, by a pure map compatible with the steps |

A compiler that performs these transformations needs exactly these laws. The parser library performs some of them as normalizations (chapter 20), so it needs its iteration to satisfy them.

**Traces and iteration are interdefinable.** Given iteration, the trace of p : A + U → B + U enters on the left and iterates p with U continuing:

tr(p) = ι₁ ⨾ (p ⨾ (id + ι₂))†.

Given a trace, iteration feeds a step back through the codiagonal ∇ = [id, id] : X + X → X:

p† = tr(∇ ⨾ p).

The two constructions are inverse to each other, and they turn lawful operators into lawful operators **[Standard: Hasegawa 1997; Bloom and Ésik 1993, from memory]**. In the library they are `Traced.OfElgot` and `Elgot.OfTraced`. `Partial.Feedback` is in fact defined as `Traced.OfElgot(Partial.Loops)`, and the tests check that turning it back into an iteration operator satisfies the Elgot laws again **[Tested]**.

### 19.4 Fixed points: Conway operators

The product row has its own fixed-point structure.

**Definition 19.3 (Conway operator).** A **parameterized fixed-point operator** on a promonad P with a strength over products sends p : A × X → X to p† : A → X, such that p† = ⟨id, p†⟩ ⨾ p, together with naturality, dinaturality, the diagonal law (p†)† = (⟨id, π₂⟩ ⨾ p)† and uniformity, which are the laws of section 19.3 with products in place of coproducts. **[Standard: Bloom and Ésik 1993; Hasegawa 1997, from memory]**

As for coproducts, a Conway operator and a trace on products determine each other, by p† = tr(p ⨾ Δ) and tr(p) = ((id × π₂) ⨾ p)† ⨾ π₁ **[Standard: Hasegawa 1997, Hyland, independently, from memory]**. In the library they are `Conway.OfTraced` and `Traced.OfConway`.

In a lazy language, fixed points over products are the familiar knot-tying definitions: `lazy val xs: LazyList[Int] = 1 #:: xs.map(_ * 2)`. In a strict language they are almost useless. To compute ⟨id, p†⟩ ⨾ p on an argument a, a strict program must compute p†(a) *before* it runs p, which means computing p†(a) before computing p†(a). The only program that satisfies the equation for every p is the one that never terminates: it satisfies it because both sides diverge **[Proved]**. Useful recursion in a strict language needs a delay. Chapter 16 used the delay that function types provide, the η-expansion `a => k(a)`, and the library keeps that form of recursion separate, as `Recursion` (section 19.6). It has no useful Conway operator on 𝒫, and states none.

### 19.5 Duality: recursion is iteration read backwards

The rows of the grid are dual. The coproducts of a category are the products of its opposite (section 3.7), so a step p : X → A + X of P is an arrow A × X → X of Pᵒᵖ, and its iteration X → A is an arrow A → X of Pᵒᵖ. The equation p† = p ⨾ [id, p†], read backwards, is p† = ⟨id, p†⟩ ⨾ p. Every law of an Elgot operator on P is the corresponding law of a Conway operator on Pᵒᵖ **[Proved]**: an iteration operator is a Conway operator on the opposite category.

The library makes this a construction, `Conway.OfElgot`, together with its inverse `Elgot.OfConway`. Applied to the loops of 𝒫, it gives the only product row of the grid that the library has:

```scala library
object PartialFixedPoints     extends Conway.OfElgot(Partial.Loops)
object PartialProductFeedback extends Traced.OfConway(PartialFixedPoints)
```

`PartialFixedPoints` computes nothing new: its fixed points are while loops. Its value is as a check. The tests run the generic Conway and trace specifications on 𝒫ᵒᵖ, and they pass **[Tested]**. So the duality is not only a remark but a fact the test suite confirms, and the same specification code serves both rows.

### 19.6 Recursion at arrow types

A grammar rule refers to itself by name: `json` is an array of `json` values. That is neither a trace nor a fixed point over products, but a fixed point of a function from *arrows* to arrows,

fix : (P(A, B) → P(A, B)) → P(A, B), fix(f) = f(fix(f)).

It lives one level up: P(A, B) is an object of 𝒮 (the type of arrows), and `fix` is a fixed point in 𝒮 at that type, not an operation of the category of arrows. The library calls it `Recursion(P)`. Section 16.4 showed its instance for 𝒫, `Partial.Knots`, defined for every f because the type of programs contains the program that never terminates. Rules that call each other, such as the expression and term rules of an arithmetic grammar, need a fixed point of a *family* of arrows, `fixFamily`. Bekić's theorem says that a family can be solved one arrow at a time, by nested fixed points, but the nesting applies the definition exponentially often in the number of rules; the library solves the family at once, with one knot per arrow **[Standard: Bekić 1969, from memory]**.

In a cartesian closed category, recursion at function types and Conway operators are closely related: a fixed point of p : A × X → X at X = (C ⇒ D) is a recursive function definition with parameter A **[Standard: from memory]**. The library does not derive one from the other, because in 𝒮 neither exists for all arguments, and the guarded versions that do exist are simpler to state separately.

### 19.7 Guarded iteration and recursion in 𝒮

Section 16.5 showed that 𝒮 cannot have an iteration operator defined on all steps: running a loop that never stops would be a total program of type `Unit` → `Nothing`. What it can have is iteration that is correct for steps that make **progress**. Goncharov, Schröder and their coauthors developed **guarded** iteration and **guarded traces** in general: the operator is defined only on, or required to satisfy its laws only on, steps that are guarded in a sense the category specifies **[Standard: Goncharov, Schröder, Rauch and Piróg 2017; Goncharov and Schröder 2018, from memory]**.

The library's guarded operators are a simple form of this idea. For state transformers whose state has a `Measure`, `StateT.GuardedIteration` runs a step while it continues, and fails as soon as a continuing step does not decrease the measure. Every run stops, and for **guarded** steps, which always decrease the measure when they continue, the result is the iteration of the step.

```scala library
given StringIsMeasure: String is Measure:
  def measure(s: String): Int = s.length

object Remaining extends StateT[String](Monad.OptionIsMonad)
object Steps     extends StateT.GuardedIteration(Remaining, ClassicalMonad.OptionIsClassical)

type Step = Unit -> String -> Option[(Either[Unit, Unit], String)]

val skipSpace: Step = _ => s => if s.startsWith(" ") then Some((Right(()), s.tail)) else Some((Left(()), s))
val stuck: Step     = _ => s => Some((Right(()), s))

val skipped: Option[(Unit, String)] = Steps.iterate[Unit, Unit](skipSpace)(())("   x")  // Some(((), "x"))
val stopped: Option[(Unit, String)] = Steps.iterate[Unit, Unit](stuck)(())("x")         // None
```

`skipSpace` is guarded: it continues only after consuming a space. `stuck` continues without consuming anything; in 𝒫 its loop would never stop, and here it fails.

The laws then come in two parts.

- For guarded steps, all Elgot laws hold **[Tested]**, and so do the trace laws of the feedback derived from it, `Traced.OfElgot`, on loops whose continuing steps consume input.
- For unguarded steps, the fixed-point law fails, since the loop stops where unrolling it would continue. The tests record this as a counterexample **[Tested: counterexample]**.
- **Yanking fails** for the guarded trace, for every input. Yanking feeds the braiding back into itself, and the braiding passes a value to the feedback wire without consuming anything: it is the simplest unguarded loop. So tr(β) fails instead of being the identity **[Tested: counterexample]**. The guarded trace satisfies all other trace laws on guarded arguments.

`StateT.GuardedRecursion`, from section 16.6, is the same idea for `Recursion`. A recursive call that comes after the measure has decreased runs, one that does not fails. Its law fix(f) = f(fix(f)) holds for guarded f **[Tested]** and fails for left-recursive f **[Tested: counterexample]**.

### 19.8 The grid in the library

| | strength | trace | fixed point / iteration |
| --- | --- | --- | --- |
| **×**, in 𝒫 | `Partial.Parallel` | via duality only: `Traced.OfConway` on 𝒫ᵒᵖ (tests) | via duality only: `Conway.OfElgot(Partial.Loops)` (tests) |
| **×**, Kleisli | `Kleisli.ProductStrength` | — | — |
| **+**, in 𝒫 | `Partial.Choice` | `Partial.Feedback` | `Partial.Loops` |
| **+**, guarded state | `Kleisli.CoproductStrength` | `Traced.OfElgot` of guarded loops (tests) | `StateT.GuardedIteration`, via `Kleisli.ElgotOf` |
| arrow types | | | `Partial.Knots`; guarded: `StateT.GuardedRecursion` |

The bridges between columns and rows, all generic:

| Construction | From | To |
| --- | --- | --- |
| `Traced.OfElgot` | iteration | trace on coproducts |
| `Elgot.OfTraced` | trace on coproducts | iteration |
| `Traced.OfConway` | Conway operator | trace on products |
| `Conway.OfTraced` | trace on products | Conway operator |
| `Conway.OfElgot` | iteration on P | Conway operator on Pᵒᵖ |
| `Elgot.OfConway` | Conway operator on P | iteration on Pᵒᵖ |

### 19.9 What the theory guarantees

For a lawful iteration operator, the loop refactorings of section 19.3 are sound, and an iteration operator and a trace can be used interchangeably. For guarded operators the guarantee is split: every run stops, always; the refactorings are sound for guarded steps. The theory does not say whether a given step is guarded. For parsers that is a property of the grammar, and chapter 20 shows how the guard turns a grammar that would loop into one that fails.

### 19.10 Set and Scala

In the category of sets and partial functions, every step has an iteration, the least fixed point, and the product row is full as well, through the order on partial functions. In Scala, strictness empties the product row except by duality, non-termination places unguarded iteration and recursion in 𝒫, and in 𝒮 there remain guarded iteration and recursion, total by construction and lawful where the program makes progress.

### References for chapter 19

**Cited from memory, not consulted**

- André Joyal, Ross Street and Dominic Verity, "Traced monoidal categories", *Mathematical Proceedings of the Cambridge Philosophical Society* 119, 1996.
- Nick Benton and Martin Hyland, "Traced premonoidal categories", *Theoretical Informatics and Applications* 37, 2003.
- Masahito Hasegawa, "Recursion from cyclic sharing: traced monoidal categories and models of cyclic lambda calculi", *TLCA 1997*.
- Calvin C. Elgot, "Monadic computation and iterative algebraic theories", *Logic Colloquium 1973*, 1975.
- Stephen L. Bloom and Zoltán Ésik, *Iteration Theories*, Springer, 1993.
- Jiří Adámek, Stefan Milius and Jiří Velebil, "Elgot theories: a new perspective on the equational properties of iteration", *Mathematical Structures in Computer Science* 21, 2011.
- Sergey Goncharov, Lutz Schröder, Christoph Rauch and Maciej Piróg, "Unifying guarded and unguarded iteration", *FoSSaCS 2017*.
- Sergey Goncharov and Lutz Schröder, "Guarded traced categories", *FoSSaCS 2018*.
- Hans Bekić, "Definable operations in general algebras, and the theory of automata and flowcharts", IBM Laboratory Vienna, 1969 (reprinted in *Programming Languages and Their Definition*, LNCS 177, 1984).

---

## Chapter 20. Case study: parser combinators

### 20.1 The idea

A parser combinator library offers a handful of primitive parsers, which read characters, and a larger number of combinators, which build parsers from parsers: sequence, choice, repetition, lookahead, recursion. Most libraries treat each combinator as a separate feature with its own implementation. This library takes the opposite approach. Every combinator except the primitives is an operation of one of the structures of chapters 17 to 19, and its behavior is fixed by that structure's laws.

Three things follow.

- **One grammar, several interpreters.** A grammar is written against the abstract algebra, so the same grammar runs on a simple interpreter that is obviously right and on an optimizing one that is fast.
- **Laws as a specification.** The laws of the structures, specialized to parsers, are the specification both interpreters are tested against. They include the equations of parsing expression grammars, which programmers already rely on informally.
- **Optimizations as theorems.** The optimizing interpreter rewrites parsers into normal forms. Each rewrite is an instance of a law, so it cannot change what a parser does.

### 20.2 The algebra is a bundle of structures

A parser `P[A, B]` consumes a prefix of the input while turning a **semantic input** of type A into a **result** of type B. Most parsers have `Unit` as semantic input; the semantic input lets a parser receive a value computed earlier, which is what sequential composition needs.

`ParserAlgebra` takes the structures it is built from as constructor parameters, as every bundle in the library does (chapter 11):

| Parameter | Structure | Chapter | Combinators |
| --- | --- | --- | --- |
| `Arrows` | promonad over a category of pure functions `-->` | 17 | `pure`, `success`, `>>`, `map`, `mapInput` |
| `Products`, `Coproducts` | cartesian and cocartesian structure of `-->`, on `Tuple2` and `Either` | 14 | used by the derived combinators |
| `Zipping` | strength over products: a Freyd category | 17 | `**`, and derived from it `&&`, `*>`, `<*`, `between` |
| `Branching` | strength over coproducts | 17 | `++`, and derived from it `\|\|` |
| `Choice` | classical restriction structure | 18 | `failure`, `~` (lookahead), `!` (negation), `attempt`, `\|>`, `+>`, `optional` |
| `Loops` | guarded iteration | 19 | `iterate`, and derived from it `repeated`, `times`, `atLeast`, `separatedBy` |
| `Knots` | guarded recursion at the types of parsers | 19 | `recursive` |

An interpreter chooses the structures and implements five primitives: `lift`, which includes Scala functions among the pure functions `-->`; `literal` and `regex`, which read the input; `rule`, which names a parser for error messages; and `diagnose`, which runs a parser. Every other combinator is defined once, in `ParserAlgebra`, from the structures. For instance:

- `p && q` = Δ ⨾ (p ** q): run both on the same semantic input, by duplicating it and running them side by side;
- `p *> q` = (p && q) ⨾ π₂: keep the right result;
- `p || q` = (p ++ q) ⨾ ∇: run the parser on the side the semantic input is on, into a common result;
- `p +> q` = (p ⨾ ι₁) |> (q ⨾ ι₂): ordered choice that tags which alternative succeeded;
- `p.repeated` iterates a step that runs p once more and appends its result, or stops where p fails.

The semantic types are fixed: `Unit` for no value, `Tuple2` for pairs, `Either` for alternatives, `Nothing` for the impossible, `Vector` for repetitions. An interpreter may override a derived combinator with a faster implementation of the same equation, and the optimizing interpreter does so for the repetitions.

### 20.3 A grammar, written once

A grammar takes the algebra as a `tracked` parameter, so that its parsers have the algebra's own parser type (section 11.2). Here is a grammar for nested lists of numbers, such as `[1, [2, 3], []]`:

```scala library
import parrot.parser.*

enum Tree:
  case Leaf(n: Int)
  case Node(children: Vector[Tree])

final class Trees(tracked val algebra: ParserAlgebra):
  import algebra.*

  val spaces: P[Unit, String]           = regex("[ ]*".r)
  def token(s: String): P[Unit, String] = literal(s) <* spaces

  val number: P[Unit, Int] =
    (regex("[0-9]+".r) <* spaces).map(lift[String, Int](_.toInt)).rule("number")

  val tree: P[Unit, Tree] = recursive[Unit, Tree] { rec =>
    val leaf  = number.map(lift[Int, Tree](Tree.Leaf(_)))
    val items = rec.separatedBy(token(",")) |> pure(lift[Unit, Vector[Tree]](_ => Vector.empty))
    val node  = items.between(token("["), token("]")).map(lift[Vector[Tree], Tree](Tree.Node(_)))
    (leaf |> node).rule("tree")
  }
```

The same class runs on both interpreters of the library:

```scala library
val reference = ReferenceParser()
val strict    = StrictParser()

val slow = Trees(reference)
val fast = Trees(strict)

val parsed  = strict.parse(fast.tree)("[1, [2, 3], []]")   // Success((Node(…), 15))
val failed  = strict.parse(fast.tree)("[1, [2 3]]")
val same    = reference.parse(slow.tree)("[1, [2 3]]")
```

Both failures carry the same message, `expected "," (in tree in tree) or "]" (in tree in tree) at position 7`: after `2 ` the parser expected a comma or a closing bracket, inside two nested trees. Section 20.6 explains where that message comes from.

The recursive call `rec` comes after an opening bracket. That makes the recursion **guarded** (section 16.6): every recursive call sees less input than the call that encloses it, so the parser terminates on every input.

### 20.4 The reference interpreter

The reference interpreter is meant to be obviously right, and it gets there by building nothing new. A parser is a Kleisli arrow of a monad assembled from the transformers of chapter 15:

`P[A, B]` = `A -> Input -> (Expected, Option[(B, Input)])` = `Kleisli(StateT[Input](OptionT(Writer(Expected.Furthest))))`.

Reading the monad from the outside in: a parser reads and advances the input (state), produces diagnostics whether it succeeds or not (a writer of `Expected`, section 20.6), and may fail (the failure transformer, placed between the two so that diagnostics survive failure). Every structure comes from a generic construction of the library:

| Structure | Construction |
| --- | --- |
| promonad | `Kleisli(State)` |
| strengths | `Kleisli.ProductStrength`, `Kleisli.CoproductStrength` |
| choice | `Kleisli.ClassicalOf`, of `StateT.ClassicalOf`, of a classical structure on outcomes with silent tests |
| loops | `Kleisli.ElgotOf` of `StateT.GuardedIteration`, measured by the length of the remaining input |
| recursion | `StateT.GuardedRecursion`, measured the same way |

The only parser-specific code is the five primitives, about fifty lines. Backtracking, for instance, is not implemented anywhere: it is what `StateT.ClassicalOf` does with ordered choice, running the second alternative from the state the first one started with. The reference interpreter is slow and not stack-safe on deeply nested input, and that is acceptable, because its job is to be the specification.

### 20.5 Laws in two tiers

`ParserLaws` collects the laws of the structures, stated for parsers in the vocabulary of parsing expression grammars **[Standard: Ford 2004, from memory, for the PEG equations]**. Each law holds for both interpreters **[Tested]**. They come in two tiers.

**Equations** hold for results, consumed input and diagnostics alike:

| Law | Equation | Structure |
| --- | --- | --- |
| identity, associativity | `success >> p` = `p` = `p >> success`; `(p >> q) >> r` = `p >> (q >> r)` | category |
| left zero | `failure >> p` = `failure` | classical restriction |
| choice monoid | `failure \|> p` = `p` = `p \|> failure`; `\|>` is associative | override (⊳.1, unit) |
| distributivity | `h >> (p \|> q)` = `(h >> p) \|> (h >> q)` | override (⊳.4) |
| attempt | `p \|> q` = `attempt(p) >> (success \|\| q)` | section 18.6 |
| lookahead | `~p >> ~q` = `~q >> ~p`; `~(~p >> q)` = `~p >> ~q` | R2, R3 |
| negation | `!!p` = `~p`; `~p >> !p` = `failure`; `~p \|> !p` = `success` | complement |
| unfolding | `p.iterate` = `p >> (success \|\| p.iterate)`, `recursive(f)` = `f(recursive(f))` | Elgot, Recursion; for guarded arguments |

**Inequations** p ⊑ q say that p and q have the same results and consume the same input, and that q reports at least what p reports:

| Law | Inequation |
| --- | --- |
| right zero | `failure` ⊑ `p >> failure` |
| R1 | `~p >> p` ⊑ `p` |
| R4 | `~(p >> q) >> p` ⊑ `p >> ~q` |

Section 18.7 explained why these three cannot be equations: lookahead is silent, and `p >> failure` reports what p expected before the failure. The tests also record what does *not* hold: choice does not distribute over what comes after it, `p ** q` depends on the order in which p and q consume input, and the guarded fixed-point law fails for left-recursive rules **[Tested: counterexample]**.

### 20.6 Diagnostics

**What a parse reports.** When a parse fails, the useful question is how far it got and what it would have accepted there. A parse therefore reports an `Expected(position, expectations)`: the furthest position at which something failed, and the set of things that were expected there. Each expectation is a label, such as `"]"` or `number`, together with its **context**, the names of the rules that enclosed it.

**Why a join-semilattice.** Diagnostics are combined whenever two parsers have run: in sequence, and in an ordered choice whose first alternative failed. Combination keeps the further position, and at equal positions unites the expectations. Positions form a chain under `max`, sets form a semilattice under union, and this combination is their **lexicographic** product: (p, X) ⊑ (q, Y) when p < q, or p = q and X ⊆ Y. The lexicographic product of a chain with a join-semilattice is again a join-semilattice, with (−1, ∅) as least element **[Proved]**. So by section 15.3, diagnostics are a commutative idempotent monoid, `Expected.Furthest`, and their order is the order of section 14.7.

The laws force most of this. The choice monoid needs an associative combination with a unit. Distributivity needs more: `(h >> p) |> (h >> q)` runs h twice where p fails, and section 18.7 showed that the two sides then report the same only if x · y · x = x · y, so in particular x · x = x **[Proved]**. Commutativity is not forced. It is a choice, and it makes the report independent of the order in which the alternatives were tried.

**A writer, not an exception.** Diagnostics are produced on success too. `literal("a").repeated` on `aab` succeeds after two `a`s, and reports that it expected another `a` at position 2. That report matters when the parse continues and fails *later at the same position*: then the error message lists both what the repetition would have accepted and what came next. With the `Writer` monad of chapter 15, this is not a special case but the definition: output is produced and combined in sequence whether the parser succeeds or fails.

**Silent tests.** Lookahead `~p` and negation `!p` report nothing about p, and neither do `failure` and the guard of a loop or recursion. Section 18.7 gave the algebraic reason: silent tests keep R2, R3 and the complement laws exact, and keeping p's output instead would break them. There is a practical reason too. On the input `1`, the parser `!keyword *> identifier` fails because no identifier starts there. If the negation reported what `keyword` expected, the message would read "expected `if` or `while` or identifier", although `if` would make the parse fail as well.

**Rules.** `rule(p, label)` runs p unchanged. Where p fails at or before its starting position, it replaces p's report by `label` at the start: the reader learns that a `number` was expected, not that `/[0-9]+/` was. Where p failed further on, it keeps p's report and adds `label` to the context of each expectation, which produces the `(in tree in tree)` of section 20.3. Adding a label to every expectation preserves joins, so it is a homomorphism of semilattices, and `rule` preserves ⊑ **[Tested]**. A rule does not change results or consumed input, which the law `ruleTransparent` checks **[Tested]**.

**Parsers are enriched over preorders.** For each A and B, ⊑ is a preorder on the parsers `P[A, B]`. Section 4.3 showed that a preorder is a category enriched over truth values, so each hom of parsers is itself a small category. And every combinator preserves ⊑: if p ⊑ p′ and q ⊑ q′, then `p >> q` ⊑ `p′ >> q′`, and likewise for `|>`, `**` and `rule` **[Tested]**. Monotone composition is exactly what makes the category of parsers a category enriched over **Pre**, the category of preorders and monotone maps, with the product of preorders as tensor (Definition 4.1). Forgetting the preorders gives back the underlying category (Definition 4.5), the parsers the library runs. Here enrichment is not decoration: it is how the law table can say "these two parsers are the same, except that one gives better error messages", and how a test can check that no combinator makes error messages worse.

### 20.7 The optimizing interpreter

`StrictParser` represents a parser as a syntax tree of `Node`s over reified pure functions `Fn` (chapter 17's "promonad as data"). It implements the structures with **smart constructors**: functions that build a node and rewrite it towards a normal form on the way. Each rewrite is a law read from left to right.

| Rewrite | Law |
| --- | --- |
| `success >> p` and `p >> success` become `p` | identity |
| `(p >> q) >> r` becomes `p >> (q >> r)`, and adjacent pure functions are composed | associativity, functoriality of `pure` |
| `Δ ⨾ (p ** q)` becomes `Pair(p, q)`; `Pair(p, q) ⨾ π₂` becomes `SkipThen(p, q)` | definitions of `&&` and `*>` |
| `(p \|> q) ⨾ f` becomes `(p ⨾ f) \|> (q ⨾ f)` for pure f | postcomposition with a *total* arrow distributes **[Proved]** |
| nested choices are flattened; `failure` alternatives are dropped | choice monoid |

The fourth row deserves a remark. Section 18.5 showed that choice does not distribute over what comes after it. But that failure needs an arrow that can fail after one alternative has committed, and a pure function cannot fail. For total f, the domain of p ⨾ f is the domain of p, and the equation holds. The rewrite lets a `map` over a choice be pushed into its alternatives, where it fuses with whatever they already compute.

The tests assert the normal forms: `literal("a") && literal("b")` is the node `Pair(Literal("a"), Literal("b"))`, which never builds a pair of inputs, and `literal("a") |> literal("b") |> literal("c")` is a single `Choice` of three literals. Regular expressions in a simple fragment are compiled to a hand-written `Scanner` that agrees with `java.util.regex` on that fragment **[Tested]**.

**Dispatch.** A `Choice` with many alternatives, such as the values of JSON, should not try them one by one. Each node carries a static summary, `Info(first, nullable)`, computed from its structure: a set of characters and a flag. The summary is correct if it satisfies

> if the parser succeeds at a position whose next character is c, then c ∈ first, or the parser is nullable and consumed nothing.

A choice then precomputes, for each character, the alternatives whose summary allows it, and at run time looks at the next character and tries only those. Skipping an alternative is sound, because it would have failed.

**A bug found by a law.** The first version of `Info` summarized two kinds of node too narrowly: regular expressions outside the scanner's fragment, which it does not analyze, and repetitions whose item may consume nothing, so that the next character can belong to the separator. Both violate the invariant. The random test of the distributivity law, `h >> (p |> q)` = `(h >> p) |> (h >> q)`, run on the optimizing interpreter, found a grammar for which dispatch skipped an alternative that would have succeeded. The fix summarizes such patterns as "may start with any character, or consume nothing", and adds the separator's first set to such repetitions **[Tested]**. No one had written a test for dispatch on separators; the law tested it anyway.

**Diagnostic mode.** Skipping alternatives is sound for results but not for diagnostics: a skipped alternative would have failed and reported what it expected. So `StrictParser` has two modes. The fast mode dispatches and records no diagnostics at all. The diagnostic mode tries every alternative in order and records failures exactly as the reference does. `parse` runs the fast mode, and only if it fails runs the diagnostic mode for the error message. Since parsers are deterministic, the second run takes the same path to the same failure.

**Left recursion, an extension.** A left-recursive rule, such as `expr ::= expr "+" "1" | "1"`, calls itself without consuming input. Under guarded recursion that call fails, so the reference interpreter parses only the base case. `StrictParser` goes further: it detects the call, lets it fail once to obtain a **seed**, then reruns the rule with the seed as the call's result, and repeats while the parse grows **[Standard: Warth, Douglass and Millstein 2008, from memory]**. On `1+1+1` it returns `((1+1)+1)`. This is an extension beyond the specification, and documented as one: the guarded fixed-point law fails for left-recursive rules in both interpreters, in different ways, and the tests record both counterexamples **[Tested: counterexample]**.

### 20.8 Agreement

The core invariant of the library is that `StrictParser` agrees with `ReferenceParser` on every grammar without left recursion: the same results, the same consumed input, and the same diagnostics. Three kinds of test check it.

- The laws of section 20.5, for both interpreters.
- A random-grammar test: a small language of grammar terms, covering every combinator, is interpreted in both algebras, and the outcomes are compared on random sources and semantic inputs **[Tested]**. During development, a longer run over 100,000 grammars, each on 20 sources and 6 semantic inputs, found no disagreement.
- The JSON grammar of the library, written once against `ParserAlgebra`, run on both interpreters over the JSON test suites in the repository.

### 20.9 Performance

The categorical structure costs nothing at run time in the optimizing interpreter: the structures are used at construction time, and what runs is a tree of specialized nodes over a mutable state, without intermediate tuples or `Either`s. On the development machine, at the time of writing, `StrictParser` parses the three documents of the nativejson-benchmark at about 110 MiB/s, and validates all 34 documents of its JSON_checker suite correctly. The reference interpreter is far slower, which does not matter for a specification.

### 20.10 What the theory guarantees

A grammar written against `ParserAlgebra` behaves the same on every lawful interpreter, up to diagnostics where the laws are inequations. Refactoring a grammar by a law, such as factoring a common prefix out of a choice (distributivity) or reassociating a sequence, does not change what it parses. The optimizing interpreter's rewrites are laws, so they cannot change behavior either; what can go wrong is an analysis that is not a law, such as `Info`, and the law tests check it indirectly. Guarded loops and recursion terminate on every input. The guarantee stops at left recursion, which the reference rejects and the optimizing interpreter extends, and at the order of effects: parsers consume input, so they never commute.

### 20.11 Set and Scala

In the category of sets and relations, a grammar denotes a language, and choice is union. Parsing expression grammars are different: their choice is ordered, so a grammar denotes a partial function from inputs to results, and choice is the override of chapter 18. In Scala, the library writes that semantics as a Kleisli category of a monad built from three transformers, adds diagnostics as a semilattice writer with silent tests, and obtains every combinator from a structure whose laws are checked. The optimizing interpreter is the same semantics as data, rewritten by its own laws.

### References for chapter 20

**Cited from memory, not consulted**

- Bryan Ford, "Parsing expression grammars: a recognition-based syntactic foundation", *POPL 2004*.
- Alessandro Warth, James R. Douglass and Todd Millstein, "Packrat parsers can support left recursion", *PEPM 2008*.
- John Hughes, "Generalising monads to arrows", *Science of Computer Programming* 37, 2000 (parsers as an early application of arrows).
- S. Doaitse Swierstra and Luc Duponcheel, "Deterministic, error-correcting combinator parsers", *Advanced Functional Programming*, 1996 (static analysis of parser combinators).

---

# Part V. Map and tools

## Chapter 21. The boundary map

### 21.1 What this chapter does

This chapter collects the results of the document into one map of what category theory looks like in Scala, compared with Set. It is meant to be consulted, not read straight through.

### 21.2 What transfers from Set

Every theorem proved from the laws of a structure holds for every lawful Scala instance of that structure, because the proof only uses the laws. Equational reasoning transfers in general, because the functor Val from 𝒮 to Set is faithful (Proposition 2.10): an equation between programs can be proved by proving the corresponding equation between functions. The basic constructions transfer: 𝒮 is bicartesian closed (Proposition 14.2) and has initial algebras for strictly positive pattern functors (chapter 16). Monoids, monads, Kleisli categories and the currying adjunction all exist as in Set (chapter 15).

### 21.3 What changes

Equality of arrows is ≐, agreement on every total argument (Definition 2.5); it is established by proof or by tests, never by a program. Maps between categories must be programs, and their object maps must be type constructors. Objects must be types, possibly filtered by evidence. Homs are types, so they are countable and first-class. The uniqueness part of a universal property becomes an equational law once the mediating arrow is given by a program.

With effects, more changes. Effectful arrows run side by side only in an order, so their tensor is premonoidal, not monoidal (chapter 17). Partial arrows have domains, and a domain can be complemented only if failure can be observed (chapter 18). Loops and recursion exist for all arguments only in 𝒫; in 𝒮 they are guarded, and their laws hold for arguments that make progress (chapters 16 and 19).

### 21.4 What is lost

Subset types and quotient types are not available as type formers, so equalizers, pullbacks and coequalizers have no uniform construction, and categories whose homs are subsets or quotients, such as lawful lenses, monoid homomorphisms and Rel, are not Scala categories as they stand (chapters 6 and 7). Functors and other maps that exist only by non-constructive arguments have no Scala counterpart (chapter 5). Objects that are values need an encoding (chapter 8). Polymorphism over kinds is missing, so each kind of object needs its own class (chapter 10).

General recursion is lost from 𝒮: a bicartesian closed category with fixed points for all arrows collapses (Proposition 14.3), so 𝒮 has only guarded fixed points, and unguarded ones live in 𝒫, which in turn has no products and no terminal object. In a strict language, fixed points over products are nearly useless, since computing one requires it first (section 19.4).

### 21.5 What is gained

Polymorphic types contain only uniform families, and their elements obey free theorems: natural transformations between functors are natural without being checked, and the polymorphic identity is the identity (chapter 9). Abstraction gives a substitute for subsets and quotients that is exact as far as clients can observe. Arrows are values that programs can build, store, pass around and, when they are data, analyze and rewrite (chapter 20). And laws are code: every equation of a structure is a function returning `Boolean`, which tests check on every instance and which the law status table records (chapter 22).

### 21.6 The map

| Structure | In Set | In 𝒮 | Scala-definable? | How | Status | Chapter |
| --- | --- | --- | --- | --- | --- | --- |
| Function composition as a category | yes | yes | yes | `Total` | [Proved, given A1] | 2, 3 |
| Programs that may not terminate | — | not arrows of 𝒮 | yes | `Partial`, 𝒫 | [Proved] | 2 |
| Kleisli categories | yes | yes | yes | `OptionKleisli`, `Kleisli(M)` | [Proved] per lawful monad | 3, 15 |
| Lenses, all get/set pairs | yes | yes | yes | `Lenses` | [Proved] | 3 |
| Lawful lenses | yes | hom is a subset | by abstraction | opaque type | [Assumed: A2] plus obligation | 6 |
| A monoid as a category | yes | yes | yes | `oneObject`, `constant` | [Proved] | 3 |
| The category of monoids | yes | homs are subsets | bigger category or abstraction | homs out of free monoids are `A -> N` | mixed | 6, 15 |
| Rel | yes | composition not computable | in pieces | finite types; finitely branching relations | [Proved] for each piece | 4, 7, 8 |
| Mat | yes | yes | with encodings | singleton types and evidence; GADT vectors | outside the model | 4, 8 |
| Order on the natural numbers | yes | yes | yes | GADT of proofs, `Order` | [Proved, sketch]; GADTs [Open] | 4, 8 |
| Free category on a graph | yes | yes | yes | GADT of paths, `Paths` | [Proved] | 8 |
| Opposite category | yes | yes | yes | `opposite`, `K.op` | [Proved] | 3 |
| Categories as data | yes | not as 𝒮-categories | yes, with partial composition | `CategoryData` | laws with side conditions | 8 |
| Functors, bifunctors, profunctors | yes | must be programs | yes | `Functor`, `Bifunctor`, `Profunctor` | [Tested]; composition law free under A2 | 12 |
| Non-computable functors | yes | no | no | — | [Proved] | 5 |
| Natural transformations between endofunctors | yes | yes | yes | polymorphic functions | natural under A2; uniformity [Open] | 9, 13 |
| Functor categories in general | yes | no hom type in general | no | — | [Open] | 13 |
| Yoneda lemma for endofunctors on 𝒮 | yes | yes | yes | `toYoneda`, `fromYoneda` | [Proved, given A1, A2] | 13 |
| Equivalence of categories | yes | yes | yes | examples | [Proved] for the examples | 13 |
| Terminal, initial, products, coproducts, exponentials | yes | yes | yes | `Total.Product`, `Total.Coproduct`, `Total.Exponential` | [Proved]; laws [Tested] | 14 |
| Products and a terminal object in 𝒫 | — | — | no | pairs are only a symmetric monoidal structure, `Partial.Product` | [Proved] | 14, 18 |
| Monoidal, symmetric, cartesian, cocartesian, closed structure | yes | yes | yes | `Monoidal` … `Closed` | [Tested] | 14 |
| Joins; semilattices | yes | yes | yes | `Semilattice` | [Tested] | 14, 15 |
| Equalizers, pullbacks | yes | no uniform construction | no | ad hoc representations | [Open] in general | 6 |
| Coequalizers, quotients | yes | no uniform construction | by setoids, canonical forms, abstraction | — | per workaround | 7 |
| Subobject classifier | yes | no | no | `Boolean` classifies decidable subsets | — | 14 |
| Monads and transformers | yes | yes | yes | `Monad`, `Writer`, `OptionT`, `StateT` | [Tested] | 15 |
| Monoid and comonoid objects | yes | yes | yes, for kind \* | `Monoid`, `Semilattice`, `Comonoid` | [Tested] | 15 |
| Currying adjunction | yes | yes | yes | `curry`, `uncurry` | [Proved] | 15 |
| Free monoid adjunction | yes | as ordinary categories | partly | `foldMap` | [Proved] | 15 |
| Initial algebras | yes | for strictly positive functors | yes | data types, `Fix`, `fold` | [Proved, given C2, A1] | 16 |
| Loops and recursion for all arguments | yes, partial functions | collapses 𝒮 | in 𝒫 | `Partial.Loops`, `Partial.Knots` | [Proved]; laws [Tested] | 16, 19 |
| Guarded loops and recursion | — | yes | yes | `StateT.GuardedIteration`, `StateT.GuardedRecursion` | [Tested] for guarded arguments | 16, 19 |
| Final coalgebras, codata | yes | outside the model | `LazyList` | — | [Open] | 16 |
| Polymorphic types as ends, free theorems | no counterpart in the same form | yes | yes | polymorphic functions | [Assumed: A2] | 9 |
| Categories of type constructors | yes | yes | yes, one class per kind | `Category1` | [Proved] | 10 |
| Promonads | yes | yes | yes | `Promonad`, `Kleisli` | [Tested] | 17 |
| Strength; Freyd categories | yes | yes | yes | `Strong`, `Strong.Bistrong`, `Freyd` | [Tested]; interchange [Tested: counterexample] | 17 |
| Restriction categories | yes | yes | yes | `Restriction`; `Partial.Domains`, `Kleisli.OptionDomains` | [Tested] | 18 |
| Classical restriction, override | yes | for observable failure only | yes | `Classical` | [Tested]; 𝒫 not classical [Proved] | 18 |
| Restriction products | yes | in 𝒫 | not stated | `Partial.Product` underneath | [Standard] | 18 |
| Traces | yes | on coproducts; on products only by duality | yes | `Traced` and its bridges | [Tested]; guarded yanking [Tested: counterexample] | 19 |
| Conway and Elgot operators | yes | iteration in 𝒫; guarded in 𝒮 | yes | `Conway`, `Elgot` and their bridges | [Tested] | 19 |
| Parser combinators as structure | — | yes | yes | `ParserAlgebra`, two interpreters | [Tested] | 20 |
| Parsers enriched over preorders | — | yes | yes | ⊑ on diagnostics, monotone combinators | [Tested] | 20 |

### 21.7 Features outside the model

Code may use any Scala feature. Unless a chapter says otherwise, the theory says nothing about the following.

| Feature | Status |
| --- | --- |
| Subtyping, variance, `Any` and its methods | outside the model |
| Implicit conversions | outside the model |
| Match types, singleton types, compile-time operations | outside the model; useful for naming objects (chapter 8) |
| Path-dependent types, `tracked` parameters | used by the encoding (chapter 11); outside the model as dependent types |
| GADTs | plausibly encodable; parametricity under type refinement [Open] |
| Shared mutation, I/O | excluded by C1; modeled by monads (chapter 15) |
| Local mutable state, created and discarded within one call, as inside `StrictParser` | allowed by C1, which forbids only effects observable from outside; not checked by capture checking alone |
| Exceptions, non-termination | excluded from 𝒮 by C2; non-termination is the business of 𝒫 |
| `null`, `eq`, casts, type tests, reflection | excluded by C3 |
| By-name parameters, `lazy val` | semantically neutral under the contract (section 2.7) |
| `LazyList` and other codata | outside the model (chapter 16) |
| `Double`, `Float` | not data types; usable with a lawful `Eq` (section 2.2) |
| Concurrency | outside the model |

### References for chapter 21

All results are cited in the chapters listed in the table.

---

## Chapter 22. Tools and workflow

### 22.1 What each tool checks

| Tool or option | Checks | Does not check | Status |
| --- | --- | --- | --- |
| The Scala compiler | types | laws, the contract | stable |
| `-source:future`, `-language:experimental.modularity` | the type-class syntax (`is`, `Self`) and `tracked` parameters used throughout | — | experimental [checked] |
| `-language:strictEquality` | no `==` without a `CanEqual` instance; no `==` on functions | custom `equals` | stable [checked] |
| `Matchable` warnings, under `-source future-migration` or later | pattern matches on `Any`, unbounded type parameters and abstract types | casts | stable [checked] |
| `-Yexplicit-nulls` | `null` in ordinary reference types; Java APIs return `T \| Null` | — | experimental **[Checked: Scala 3.10.0]**, enabled in the library |
| Capture checking | pure function types `->`; tracked capabilities | local mutable variables (without separation checking); exceptions | experimental, described as maturing [checked]; enabled for the library and its tests |
| Separation checking | aliasing of exclusive capabilities, including local mutable variables | — | experimental, in flux [checked] |
| Safe mode | no unchecked casts or matches, no `caps.unsafe`, no reflection, all mutation tracked, safe global objects only | exceptions | experimental [checked] |
| Stainless | termination; absence of some run-time errors; contracts; laws of verified type-class hierarchies | code outside its subset; very likely the modularity syntax | Scala 3.5.0 and later [checked] |
| ScalaCheck, through the library's `LawSuite` | laws on generated arguments and sample points | anything beyond the samples | stable |
| `docs/tutorial/check-snippets.py` | every Scala block of this document compiles, or fails to compile where it should | what the code means | this repository |
| Nothing | `eq`, `hashCode`, `toString`, custom `equals`, strict positivity, guardedness, code marked `@assumeSafe`, assumptions A1–A3 | | |

### 22.2 The library's set-up

The library is built with sbt. The library and its tests are compiled with the flags of the preface plus capture checking, so that `A -> B` is the type of pure functions in every signature. The tests draw functions from ScalaCheck, which is not compiled with capture checking, and use them as pure functions; capture checking trusts code it has not checked, so that is a promise **[Convention]**. Warnings are not errors, but the build has none, and the coding rules of the repository exist to keep it that way.

```sh
sbt --client compile                 # the library
sbt --client testFull                # every test; also regenerates docs/law-status.md
sbt --client "testOnly parrot.category.GridTest"
sbt --client "Test/runMain parrot.json.JsonBenchmark nativejson-benchmark"
docs/tutorial/check-snippets.py --classpath target/out/jvm/scala-3.10.0/parrot/classes  # this document's code
```

In sbt 2, `test` runs only the tests affected by a change, so `testFull` is the command that checks everything. The repository also contains a Pants configuration, supported via the in-repo `scala_override` plugin.

Keep code that keeps the contract, the *core*, separate from code at the edges that performs I/O, interacts with Java libraries or loops forever. In the library, the edges are the `Partial` programs, which may not terminate, and the benchmark, which reads files.

### 22.3 Laws as tests

Section 3.10 introduced the pattern: a law is a method that returns `Boolean`, the arrows it compares are observed at sample points by an `Observable`, and a property test calls it on generated arguments. The library applies the pattern uniformly, with four refinements.

- **One specification per structure, one test per instance.** Each structure has an abstract test class, such as `RestrictionSpec` or `ElgotSpec`, that checks every law of the structure. An instance's test extends it with the instance, and the specification finds the instance's **fixture**, generators for arrows and for observations, as a given. Adding an instance means writing a fixture, not tests.
- **Sharp generators.** Arrows are generated to exercise the cases where laws break: failure, partiality, consumption of input, outputs that differ. Sample points are generated afresh for each property.
- **Congruence by construction.** Agreement on samples is not a congruence: two functions that agree at the sample points can be told apart once composed with a third. So congruence laws, "equal arrows give equal results", take a **variant** of an arrow, an arrow equal to it by construction but represented differently, never an arrow that merely agrees on samples.
- **Conditional laws by targeted generators.** A law with a premise, such as uniformity of iteration or the guarded fixed-point law, gets a generator that produces only arguments satisfying the premise, so that no generated case is wasted.

Laws that hold only up to diagnostics are checked with a `Preorder` instead of an `Observable` (section 20.5). Laws that do *not* hold are kept too: a **counterexample** test searches for a witness, and it fails if it finds none. A counterexample test records what the library's structures are not, such as premonoidal tensors that are not monoidal, which is as much part of the specification as what they are.

### 22.4 The law status table

Every run of the law tests writes `docs/law-status.md`, a table with one row per law and instance and one of three statuses: *Tested*, *Fails (counterexample)*, or *Fails*, which is a bug. The status labels **[Tested]** and **[Tested: counterexample]** in this document cite that table. Because it is regenerated by every test run and checked in, a change that breaks a law shows up both as a failing test and as a changed line in the table.

### 22.5 Checklist for a new category or structure

1. Decide the base: the category (or promonad, or monoidal structure) your structure is on, and pass it as a `tracked` parameter (chapter 11).
2. Write the operations, and check them against the contract: capture checking for C1, Stainless or a promise for C2, review for C3.
3. Write the laws as methods returning `Boolean`, each with its equation in the documentation.
4. Decide the observations used to compare arrows, and write a fixture with sharp generators and a variant.
5. Prove each law on paper where it is easy; add a Stainless lemma where the code fits Stainless's subset; extend the structure's specification in every case.
6. Record what does not hold as counterexample tests.
7. List what you wanted but could not express, and choose a workaround from chapters 6 to 8.

### 22.6 Known gaps

The largest gap is A3 of appendix B: no theorem says that contract-keeping Scala programs behave like their translations into the formal core, so every theorem of this document applies to Scala through an unproved correspondence. Close behind are A1 and A2, the fundamental lemma and parametricity, which are theorems for calculi like the core but have not been proved for Scala. On the tooling side, it is not known whether Stainless accepts code written with capture checking or with the modularity syntax, so proofs and tests use two dialects. Guardedness, which the total loops and recursion of chapters 16 and 19 rely on for their laws, is not checked by any tool: the library guarantees termination, and the tests check the laws on guarded arguments. All code in this document is compiled by the snippet checker, and the library's laws are tested, but nothing here has been verified by a proof assistant.

### References for chapter 22

**Consulted while writing this chapter**

- The Scala 3 reference pages and the Stainless sources listed in chapters 2 and 3.

---

# Appendices

## Appendix A. The formal core

The results of this document are stated for Scala, but their proofs, where they go beyond the laws of a structure, rely on a small formal language, the **core**, of which the pure, representation-independent fragment of Scala is meant to be a faithful image. This appendix describes the core and its relationship to Scala. The core is a *partial* language: it has general recursion, so its programs may fail to terminate. The total programs, and with them the category 𝒮, are carved out of it by the relation of section 2.6.

### A.1 The language

The core is a strict polymorphic λ-calculus with data and general recursion:

- **Kinds**: \* for types, and κ → κ′ for type operators.
- **Types**: type variables; `Unit` and `Nothing`; products, sums and function types; universal types ∀X:κ. A; existential types ∃X:κ. A; type-level functions and their applications; and inductive types μX. P for strictly positive P, in which X never occurs to the left of a function arrow.
- **Terms**: the introduction and elimination forms of each type former, including pairing and projection, injection and case analysis, abstraction and application, type abstraction and application, packing and unpacking of existentials, and the constructor and case analysis of each inductive type; and **recursive function definitions**, fix f. λx. e, which bind f to the function being defined inside its own body.
- **Evaluation**: strict, call by value. A function's argument is evaluated to a value before the function is called, the components of a pair are evaluated before the pair is built, and evaluation may fail to terminate.

Recursion appears only at function types, as fix f. λx. e. That is the restriction section 2.7 explained: under strict evaluation, a recursive definition of any other type could never be evaluated. Exceptions are not part of the core; a Scala program that throws is translated as one that does not terminate (section 2.3).

### A.2 Properties

- **Determinism.** Evaluation is a partial function: a program terminates with at most one value **[Standard, from memory]**.
- **Type safety.** A well-typed program either terminates with a value of its type or runs forever; it never gets stuck **[Standard, from memory]**.
- **Canonical forms.** A closed value of a data type is a constructor tree.
- **No normalization.** Because of fix, some well-typed programs do not terminate. Totality is therefore not a property of the language but of individual programs, defined by Definition 2.5.
- **Logical relations.** Relations defined by induction on types, like ≐ of Definition 2.5 and the relations behind parametricity, can be developed for languages of this kind with operational methods, recursion included **[Standard: Pitts 2000, from memory]**. Danielsson and colleagues carve the total part out of a partial language with such a relation and prove that it forms a bicartesian closed category [Danielsson et al. 2006, checked].

### A.3 Assumptions connecting the core to Scala

| | Assumption | Used in |
| --- | --- | --- |
| A1 | **Fundamental lemma**: every program respects ≐; in particular, equal total programs are observationally equal, even inside programs that do not terminate (section 2.6). Proved for model languages of this kind with logical relations; not proved for this exact core or for Scala. | chapter 2 (𝒮 is a subcategory of 𝒫), chapter 7, and every argument that replaces equal total programs inside a larger program |
| A2 | **Parametricity**: polymorphic programs respect relations, including the abstraction theorem for existential types (section 9.3). Proved for System F, and for languages with recursion by operational methods; not proved for Scala. | chapters 6, 7, 9 and later |
| A3 | **Correspondence**: a pure, representation-independent Scala program behaves like its translation into the core, so that observational equality in Scala agrees with observational equality in the core. Not proved. | everything that applies the core's properties to Scala |

Extensionality, the principle that functions agreeing on every argument are equal, is not on the list. In 𝒮 it is the *definition* of equality (Definition 2.5), and the assumption that remains, A1, says that this definition agrees with what programs can observe.

### A.4 Translation

| Scala | Core |
| --- | --- |
| case classes, enums, `Option`, `Either`, `List`, tuples | sums, products and inductive types |
| function types `A -> B`, and `A => B` without capabilities | function types |
| recursive methods and functions, `while` loops | fix f. λx. e; a loop is a recursive function |
| `throw`, `???` | a program that does not terminate |
| generic methods and polymorphic function types | universal types |
| type members, opaque types, modules | existential types, following the approach of "F-ing modules" **[Standard: Rossberg, Russo and Dreyer 2014, from memory]** |
| type lambdas, higher-kinded type parameters | type operators |
| type classes with `Self`, givens, context bounds | records of operations passed explicitly |
| `Int`, `Long`, `Char`, `String`, `BigInt` | primitive data types with their total operations |
| GADTs | encodable with Leibniz equality **[from memory]**; not part of the core |
| match types, singleton types, subtyping, variance | not translated: outside the model |
| capabilities, mutation, I/O | not translated: excluded by C1 |

---

## Appendix B. Ledger

**Assumptions**

- **A1. Fundamental lemma** (section 2.6): equal total programs cannot be told apart by any program.
- **A2. Parametricity** (section 9.3), including the abstraction theorem for opaque types.
- **A3. Correspondence** between pure, representation-independent Scala and the formal core (appendix A).

**Conventions**

- **C1. Purity** (section 2.3). Checked by capture checking with `->`, and for local mutable variables by separation checking or safe mode; code marked `@assumeSafe` is a promise.
- **C2. Totality** (sections 2.3 and 2.6): the claim that a program is an arrow of 𝒮. Checked by Stainless on its subset; otherwise asserted. The library confines the explicit assertion to `Partial.assumeTotal`; writing a value of type `A -> B` and using it as an arrow is the implicit one. A false assertion voids every conclusion that relied on it.
- **C3. Representation independence.** Partly checked by strict equality, `Matchable` warnings, explicit nulls and safe mode; `eq`, `hashCode`, `toString` and custom `equals` are unchecked.
- **Resources.** A function that would terminate given enough stack and memory counts as total.
- **Objects of the model.** Only the types of the model count as objects, although type parameters range over all Scala types.
- **Strict positivity.** Recursive types used with `Fix` and `fold` are strictly positive (chapter 16).
- **Guardedness.** Loops and recursive definitions whose laws are relied on make progress before they continue or recurse (sections 16.6 and 19.7). Termination does not depend on it; the laws do.
- **Lifted functions.** Functions given to a parser algebra's `lift` are total and pure; the optimizing interpreter may compose, move or duplicate them (section 20.7).
- **Test functions.** The tests use ScalaCheck's generated functions as pure functions; ScalaCheck is not compiled with capture checking, so nothing checks it (section 22.2).
- **Invariants of abstractions.** The exported operations of an opaque type used as a subset or quotient preserve its invariant or equivalence (sections 6.5 and 7.6).
- **Coherence of equality.** A type has at most one `Eq` in its implicit scope, its semantic equality; a coarser equality gets a new type (section 7.4).

**Open**

- No theorem relates Scala to the core (A3). The result of Danielsson and colleagues covers a pair of model languages (section 2.11).
- Whether separation checking gives arrows that can be treated as pure, and whether a category of such arrows is enriched over a non-cartesian structure (sections 2.3 and 4.2).
- Whether Stainless accepts the modularity syntax and code compiled with capture checking (section 2.3).
- Whether every equalizer of arrows in 𝒮 has a representing type, in particular for the lens laws (section 6.3).
- Whether A1 and A2 survive GADT pattern matching (section 4.5).
- The uniformity question: whether every natural family between Scala-definable functors is given by a polymorphic program (section 9.7), and whether functor categories in general have hom types (chapter 13).
- A treatment of codata and productivity under the contract (chapter 16).
- Whether path-dependent types of run-time values can be brought into the model (section 8.3).

---

## Appendix C. Glossary

**Adjunction.** A pair of functors F ⊣ G with a natural bijection between arrows F(a) → b and arrows a → G(b). Definition 15.4.

**Arrow (morphism).** An element of a hom; in 𝒮, a contract-keeping function value up to ≐. Sections 1.1, 2.8.

**Attempt.** The operation attempt(p) = (p ⨾ ι₁) ⊳ ι₂ : A → B + A, which never fails and reports whether p succeeded. Section 18.6.

**Bicartesian closed.** Cartesian closed, with an initial object and coproducts as well. Definitions 14.1.

**Bifunctor.** A functor of two arguments, such as `Tuple2` and `Either`. Definition 12.1.

**Bistrong.** Having a left strength τ and a right strength τ′ that commute; over a symmetric monoidal category acting on itself, τ′ comes from τ by braiding. In the library, `Strong.Bistrong`. Section 17.3.

**Bundle.** A class that combines several structures by taking them as `tracked` parameters, rather than by inheritance, such as `Freyd` and `ParserAlgebra`. Section 11.3.

**Cartesian closed.** Having a terminal object, products and exponentials. Definitions 14.1.

**Category.** Objects, arrows, identities and an associative composition. Definition 1.1.

**Change of base.** Turning 𝒱-categories into 𝒲-categories by applying a structure-preserving functor 𝒱 → 𝒲 to every hom. Section 4.6.

**Classical restriction category.** A restriction category with a zero, complements of domains and joins of compatible arrows; the Kleisli category of `Option` is one, 𝒫 is not. Section 18.4.

**Coequalizer.** The categorical form of a quotient. Section 7.1.

**Comonoid.** The dual of a monoid object: an object with a counit, which deletes, and a comultiplication, which copies. Section 15.3.

**Complement.** The arrow f̄ᶜ : A → A defined exactly where f is not; negation `!p` for parsers. Section 18.4.

**Congruence.** An equivalence relation preserved by every surrounding expression. Proposition 2.3. In the library, also the law that an operation sends equal arguments to equal results, tested with variants. Section 22.3.

**Contract.** The clauses C1–C3: purity, totality, no observation of representations. Section 2.3.

**Conway operator.** A parameterized fixed-point operator on products, p† = ⟨id, p†⟩ ⨾ p, with its laws. Definition 19.3.

**Copyable effect.** An effect that produces the same outcome when performed twice as when performed once; for a writer, an idempotent monoid. Section 17.5.

**Counterexample test.** A test that searches for a witness that a law fails, and fails if it finds none. Section 22.3.

**Data type.** A type built from primitive types with tuples, `Option`, `Either`, `List` and structurally compared case classes and enums, with no functions or abstract types inside. Section 2.2.

**Diagnostics.** What a parse reports: the furthest position at which something failed and what was expected there, a join-semilattice produced as a writer effect. Section 20.6.

**Dispatch.** Choosing the alternatives of a choice to try from the next character, using a static first-set and nullability summary. Section 20.7.

**Elgot operator (iteration operator).** An operation sending a step X → A + X to an arrow X → A that runs it until it stops, with its laws. Definition 19.2.

**Endofunctor.** A functor from a category to itself; in the library, `Endofunctor(K)`. Section 12.2.

**Endoprofunctor.** A profunctor 𝒦ᵒᵖ × 𝒦 → 𝒱 on a single category; in the library, `Endoprofunctor(K, V)`. Definition 12.2.

**Enriched category (𝒱-category).** A category whose homs are objects of 𝒱 and whose identities and composition are arrows of 𝒱. Definition 4.1.

**Equalizer.** The categorical form of a subset cut out by an equation. Definition 6.1.

**Equivalence of categories.** Functors that are inverse up to natural isomorphism. Definition 13.3.

**Evidence.** A value witnessing that a type is an object of a category, passed through context bounds. Sections 3.8, 8.2, 11.4.

**Exponential.** The categorical form of a function type. Definitions 14.1.

**Faithful, full.** A functor is faithful if it is injective on each hom and full if it is surjective on each hom. Section 1.4.

**Fixture.** The generators of arrows, variants and observations that let a structure's generic law specification test an instance. Section 22.3.

**Free category.** The category of paths in a graph. Section 8.4.

**Free monoid.** The list type, with `foldMap` as the unique homomorphism extending a function. Section 15.6.

**Free theorem.** An equation about a polymorphic program that follows from its type alone. Chapter 9.

**Freyd category.** A promonad with a strength that agrees with its pure arrows and its composition. Definition 17.3.

**Functor.** A map between categories preserving identities and composition. Definition 1.3.

**Fundamental lemma (A1).** Every program respects ≐; in particular, equal total programs are observationally equal. Section 2.6.

**GADT.** An algebraic data type whose cases fix its type arguments in different ways. Section 4.5.

**Guarded.** Of a loop step or recursive definition: it continues, or calls itself, only after making progress in a measure that cannot decrease forever. Sections 16.6, 19.7.

**Hom (hom-set, hom-object).** The collection of arrows between two objects. Sections 1.1, 4.2.

**Initial algebra.** The algebra from which there is exactly one homomorphism to every other; its homomorphisms are folds. Definition 16.1.

**Initial object, terminal object.** Objects with exactly one arrow to, respectively from, every object. Definitions 14.1.

**Interchange.** The law that two arrows run side by side in either order give the same result; it fails for most effects. Section 17.4.

**Isomorphism.** An arrow with an inverse. Section 1.3.

**Join, join-semilattice.** A least upper bound, which is a coproduct in a preorder; a preorder with a least element and all binary joins. Section 14.7.

**Kleisli category.** The category of arrows `A -> M[B]` for a monad `M`. Sections 3.5, 15.2.

**Law status table.** The table `docs/law-status.md`, regenerated by every test run, that records each law and instance as tested or refuted. Section 22.4.

**Left module (left actegory).** A category 𝒦 with an action ⊘ : ℳ × 𝒦 → 𝒦 of a monoidal category ℳ, unital and associative up to coherent isomorphism; every monoidal category acts on itself. In the library, `Module`. Section 17.3.

**Left recursion.** A rule that calls itself before consuming input; guarded recursion fails the call, and `StrictParser` extends it by seed growing. Section 20.7.

**Locally small.** Having a set of arrows between any two objects; the same as Set-enriched. Section 1.5.

**Measure.** A natural number attached to the states of a computation, which guarded loops and recursion must decrease. Section 16.6.

**Monad.** An endofunctor with a unit and a multiplication satisfying the laws of a monoid; equivalently, a Kleisli triple. Definition 15.1.

**Monoid.** A set with an associative operation and a unit; a one-object category. Section 1.2. As a monoid object in a monoidal category, Definition 15.3.

**Monoidal category.** A category with a tensor and a unit, associative and unital up to coherent isomorphism. Sections 4.2, 14.5.

**Natural transformation.** A family of arrows between two functors that commutes with every arrow. Definition 13.1.

**Observable.** A test of equality that compares values by finitely many observations, sound for refuting laws. Section 3.3.

**Observational equality (≈).** Indistinguishability by every program of the language. Definition 2.2.

**Opposite category.** The same category with every arrow reversed. Definition 3.3.

**Override (⊳).** "f where f is defined, g elsewhere": ordered choice, with the axioms of Lemay and Nester. Definition 18.2.

**𝒫.** The category of Scala programs that keep C1 and C3 but may not terminate. Definition 2.7.

**Parametricity (A2).** Polymorphic programs respect relations between their type arguments. Section 9.3.

**Point.** An arrow from the terminal object; in 𝒮, a total value. Section 14.4.

**Premonoidal.** Having a tensor that is a functor in each argument separately but not jointly, because effects are ordered. Section 17.4.

**Preorder.** A reflexive and transitive relation; a category with at most one arrow between two objects; a 𝔹-category. Sections 1.2, 4.3.

**Product, coproduct.** The categorical forms of pairs and of tagged unions. Definitions 14.1.

**Product category.** The category 𝒞₁ × 𝒞₂ of pairs of objects and pairs of arrows, composed componentwise; a bifunctor is a functor out of it. Section 12.3.

**Profunctor.** A bifunctor contravariant in its first argument, such as the function type. Definition 12.2.

**Promonad.** A profunctor with a unit, including the pure arrows, and an associative composition; a category of effectful arrows over a category of pure ones. Definition 17.1.

**Recursion (structure).** A fixed-point operator at the types of arrows of a promonad, fix(f) = f(fix(f)). Section 19.6.

**Restriction, restriction category.** The restriction f̄ is the identity on the domain of f; a restriction category satisfies R1 to R4. Definition 18.1.

**Restriction product.** The weakened product of a restriction category, with π₁ ∘ ⟨f, g⟩ = f ∘ ḡ. Section 18.3.

**𝒮.** The category of Scala programs that keep the contract, up to ≐. Definition 2.8.

**𝒮-functor.** A functor between 𝒮-categories whose action on arrows is a Scala function. Definition 4.6.

**Semilattice.** A commutative, idempotent monoid; equivalently, a join-semilattice. Section 15.3.

**Setoid.** A type with an explicit equivalence relation. Section 7.4.

**Silent test.** A restriction or complement that reports nothing about the arrow it tests. Sections 18.7, 20.6.

**Strength.** An operation τ : P(A, B) → P(C ⊘ A, C ⊘ B) that carries a context along while an arrow runs, for left actions ⊘ of a monoidal category; in the library, `Strong`. Definition 17.2.

**Strictly positive.** Of a pattern functor: the recursive parameter never appears to the left of a function arrow. Section 16.2.

**Symmetric monoidal category.** A monoidal category with a braiding β that is its own inverse. Section 14.5.

**Total equality (≐).** Equality of total programs, defined type by type; on functions, agreement on every total argument. Definition 2.5.

**Trace.** Feedback: an operation P(A ⊗ U, B ⊗ U) → P(A, B), with the laws of traced monoidal categories. Definition 19.1.

**`tracked` parameter.** A constructor parameter whose singleton type is kept in the type of the constructed value, which lets structures take their bases as parameters. Section 11.2.

**Underlying ordinary category.** The ordinary category with the same objects whose homs are the sets of values of the hom types. Definition 4.4.

**Underlying 𝒮-category.** The 𝒮-category obtained from a 𝒱-category by reading each hom-object through 𝒱(I, −). Definition 4.5.

**Uniform.** Having homs given by one type constructor and structure given by single polymorphic programs. Section 4.5.

**Val.** The functor from 𝒮 to Set sending a type to its set of total values. Section 2.10.

**Variant.** An arrow equal to a given one by construction but represented differently, used to test congruence laws. Section 22.3.

**Well-pointed.** Having arrows determined by their action on points. Section 14.4.

**Writer.** The monad of a monoid W, pairing a result with an output. Sections 15.2, 17.5.

**Yoneda lemma.** Natural transformations out of a represented functor correspond to elements. Proposition 13.2.

---

## Appendix D. What the library leaves out

An earlier version of the library had more structures than the current one. Some were removed because they were wrong: they claimed laws that their code could not satisfy. Others were removed because nothing used them. This appendix lists the removals that a reader of the literature, or of the earlier version, might look for. The repository's design rationale, `docs/DESIGN.md`, has the complete list, and the git tag `pre-prune` marks the last version that contains them all.

### Removed because they were wrong

| Construct | Why | Where its job went |
| --- | --- | --- |
| Total fixed points and iteration on Scala functions | Each diverged on some input while claiming to be an arrow of the total category 𝒮. Proposition 14.3 shows that 𝒮 cannot have a fixed point for every arrow without collapsing. | Unguarded loops and recursion on 𝒫 (`Partial.Loops`, `Partial.Knots`); guarded ones in 𝒮 (chapters 16 and 19). |
| Lazy pairs as a cartesian structure | Isomorphic to ordinary pairs in 𝒮, and not a product in 𝒫, where a program can tell a diverging pair from its components. They existed only to tie the knots above. | None needed. A lazy semantics would be a separate project. |
| Strength defined as `p *** id` on a monoidal category | Every one of its laws followed from bifunctoriality, so it said nothing. Strength is structure on a profunctor over left modules (Definition 17.2). | `Strong(P, L1, L2)` and `Strong.Bistrong(P, M)`. |
| Restriction on Scala functions, `a => { p(a); a }` | In 𝒮 every arrow is total, so this is the identity. | `Partial.Domains`, on 𝒫, where it means something (chapter 18). |

### Removed because nothing used them

| Construct | Why | Bring it back when |
| --- | --- | --- |
| Ordered choice as enrichment over additive monoids | Choice distributes over composition on one side only, so it is not a monoid structure on homs compatible with composition. It is the override of a classical restriction category (chapter 18). | Never. |
| Multiplicative monoids | No client. | A client appears. |
| A second, enriched hierarchy of categories, functors and promonads, with bridges to the ordinary one | Two parallel hierarchies doubled the code. The library has one level: categories with a semantic equality on their homs, which is enrichment over setoids stated directly (section 7.4), and parsers with a preorder on their homs (section 20.6). | An enriched module gets a client. |
| Mixin traits for the parser algebra | Combinations of structures are bundles, not inheritance (section 11.3). | Never. |
| Abstract semantic types in the parser algebra | Every interpreter made the same choice: `Unit`, `Tuple2`, `Either`, `Nothing`, `Vector`. | An interpreter needs different ones. |

Comonoids were first removed for the same reason, and then restored: they are the dual of monoids, and they explain, by Fox's theorem, why the pairs of 𝒫 are not products (section 15.3).

### Not attempted

Some structures appear in the literature on effects and parsing and are absent on purpose: a general theory of codata and productivity (section 16.7), restriction products as a class (section 18.3), useful fixed points over products in a strict language (section 19.4), packrat memoization, and error recovery. Each would need a client before it earns a place.

---

## Appendix E. Concept index

Each concept is introduced where a problem needs it. This index lists, for each, the chapter that introduces it, the problem that motivates it, and the smallest example in the text.

| Concept | Ch. | Motivating problem | Minimal example |
| --- | --- | --- | --- |
| Category, isomorphism, functor | 1 | many structures share composition and identities | sets and functions; a monoid; the preorder of integers |
| 𝒫, 𝒮, the contract, total equality ≐ | 2 | Scala functions form a category only if they behave like functions; Theorem 2.4 | `loop()`; equality type by type |
| Val, faithful but not full | 2 | how far reasoning about programs as sets of values goes | the halting function is not in 𝒮 |
| Category as an interface; laws as code; `Observable` | 3 | writing a category once and checking it | `OptionKleisli`, `Lenses` |
| Opposite category | 3 | contravariance; dualities | `opposite(Total)` |
| Evidence for objects | 3, 8, 11 | categories whose objects are not all types | `withEq`; equality types |
| Enriched category; 𝔹-categories | 4 | homs of a Scala category are types, not sets | preorders as 𝔹-categories |
| Change of base into 𝒮 | 4 | the underlying category should itself be a program | 𝒱(I, −) for a Scala 𝒱 |
| Arrows are programs | 5 | equality of arrows is not decidable; composition must be computable | relations given by predicates |
| Subsets and their workarounds | 6 | lawful lenses, monoid homomorphisms | abstraction with an opaque type |
| Quotients; setoid enrichment | 7 | laws that hold only up to an intended equivalence | lists as sets |
| Objects as types; free categories | 8 | objects that are values | typed state machines as paths |
| Parametricity, free theorems | 9 | natural transformations without proofs | the polymorphic identity; rearrangements of lists |
| One kind per class | 10 | categories of type constructors | `Category1` |
| Encoding: tracked bases, bundles, evidence | 11 | duplication and missing "has a" in Parts I–II | a functor between two categories |
| Bifunctors, profunctors | 12 | pairs and `Either` map on both sides; `A -> B` is contravariant in A | `dimap` on functions |
| Natural transformations, Yoneda, equivalence | 13 | polymorphic functions and their uniformity | `headOption`; `toYoneda` |
| Universal constructions; monoidal structures | 14 | universal properties in 𝒮 need code; pairs in 𝒫 are not products | `Total.Product`; `Partial.Product` |
| Joins as coproducts in a preorder | 14 | combining reports of the furthest failure | positions under `max` |
| Monads, transformers, monoid and comonoid objects, adjunctions | 15 | making effects visible; "a monad is a monoid" made precise; why pairs in 𝒫 are not products | `Option`; `StateT` from currying; copying and deleting |
| Semilattices | 15 | a monoid that is also an order | sets under union; positions under `max` |
| Folds, iteration, recursion, guardedness | 16 | recursion beyond structural recursion; why recursion cannot be total in general | `gcd` by iteration; a balanced-parentheses recognizer |
| Promonads | 17 | Kleisli categories and syntax trees both contain the pure functions | `Kleisli.OptionKleisli`; `StrictParser`'s nodes |
| Left modules, strength, bistrong profunctors, Freyd categories, premonoidal tensors | 17 | running effectful arrows side by side | a logger with a non-commutative log |
| Commuting and copyable effects | 17 | when interchange holds and when running twice is running once | writers of commutative and idempotent monoids |
| Restriction categories; restriction products | 18 | where an arrow is defined, asked inside the category | `Option` Kleisli; 𝒫 |
| Classical restriction, override, attempt | 18 | ordered choice as a theorem; decidable failure versus divergence | `half \|> odd`; 𝒫 is not classical |
| Silent tests | 18, 20 | effects other than failure break some restriction laws | lookahead that reports nothing |
| Traces, Conway and Elgot operators, the grid | 19 | iterating and recursing effectful arrows; refactoring loops | `Partial.Feedback`; guarded `skipSpace` |
| Duality of iteration and recursion | 19 | the product row of the grid in a strict language | `Conway.OfElgot(Partial.Loops)` |
| Parser algebra as a bundle | 20 | one grammar, several interpreters, combinators with laws | nested lists of numbers |
| Diagnostics: lexicographic semilattice, tagging, ⊑ | 20 | error reports must respect the laws of choice and lookahead | `expected "," or "]" at position 7` |
| Parsers enriched over preorders | 20 | stating "the same parser, with better error messages" | monotonicity laws |
| Laws as tests: fixtures, variants, counterexamples, the status table | 22 | checking every instance of every structure, including what fails | `docs/law-status.md` |

---

## References not cited in a specific chapter

- Andreas Rossberg, Claudio Russo and Derek Dreyer, "F-ing modules", *Journal of Functional Programming* 24, 2014. (From memory.)
- Jean-Yves Girard, *Interprétation fonctionnelle et élimination des coupures de l'arithmétique d'ordre supérieur*, thesis, Université Paris VII, 1972. (From memory.)
