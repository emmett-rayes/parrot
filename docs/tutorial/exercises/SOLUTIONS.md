# Solutions to the exercises of the tutorial

Each solution is an instance of a structure of the library. The snippet checker compiles every block of this file
against the library (`docs/tutorial/check-snippets.py`). To check a solution against the laws, write the test class
that its exercise names beside the specs in `src/test/scala/parrot/category`, and run it with
`sbt --client "testOnly parrot.category.<TestClass>"`.

## Chapter 12. Functors, bifunctors and profunctors

### Exercise 12.1: `List` as a functor, and a broken one

```scala unit=Exercise1
import parrot.category.*
import Category.Type

object ListIsFunctor extends Endofunctor(Total) {
  type Self = List

  def objects[A: Type]: List[A] is Type = Type.TIsType

  def map[A: Type, B: Type](f: A -> B): List[A] -> List[B] = _.map(f)
}

// Reversing in `map` keeps `composition` only for lists that are palindromes, and breaks `identity`:
// `map(id)` reverses, and the identity does not.
object ReversingList extends Endofunctor(Total) {
  type Self = List

  def objects[A: Type]: List[A] is Type = Type.TIsType

  def map[A: Type, B: Type](f: A -> B): List[A] -> List[B] = _.reverse.map(f)
}
```

Test class: `class ListIsFunctorTest extends FunctorSpec("List", ListIsFunctor)`, with a given
`[X] => Sample[X] ?-> Sample[List[X]]`. For `ReversingList`, the law `identity` fails.

## Chapter 15. Monads, monoid objects and adjunctions

### Exercise 15.1: the exception transformer

```scala unit=Exercise1
import parrot.category.*
import Category.Type

/** Computations of a monad that may also fail with an error of type E. */
final class EitherFunctorOf[E](tracked val monad: Monad.On[Total.type]) extends Endofunctor(Total) {
  type Self[A] = monad.M[Either[E, A]]

  def objects[A: Type]: monad.M[Either[E, A]] is Type = Type.TIsType

  def map[A: Type, B: Type](f: A -> B): monad.M[Either[E, A]] -> monad.M[Either[E, B]] = {
    monad.map[Either[E, A], Either[E, B]](_.map(f))
  }
}

open class EitherT[E](tracked val monad: Monad.On[Total.type]) extends Monad(EitherFunctorOf[E](monad)) {

  def unit[A: Type]: A -> monad.M[Either[E, A]] = {
    a => monad.unit[Either[E, A]](Right(a))
  }

  def flatten[A: Type]: monad.M[Either[E, monad.M[Either[E, A]]]] -> monad.M[Either[E, A]] = {
    monad.bind[Either[E, monad.M[Either[E, A]]], Either[E, A]] {
      case Right(m) => m
      case Left(e)  => monad.unit[Either[E, A]](Left(e))
    }
  }
}

/** `Either[String, A]`: the transformer over the identity. */
object StringErrors extends EitherT[String](Monad.Identity)
```

Test class: `class StringErrorsIsMonadTest extends MonadSpec("Either[String]", StringErrors)`.

### Exercise 15.2: a semilattice, and a monoid that is none

```scala unit=Exercise2
import parrot.category.*
import Category.Type

/** Positions in a text under the maximum, with −1 for "no position". */
object Furthest extends Semilattice(Total.Products) {
  type Self = Int

  def evidence: Int is Type = Type.TIsType

  def unit: Unit -> Int = _ => -1

  def multiply: ((Int, Int)) -> Int = (a, b) => a.max(b)
}

/** Strings under concatenation, claimed to be a semilattice: `commutativity` and `idempotence` fail. */
object Concat extends Semilattice(Total.Products) {
  type Self = String

  def evidence: String is Type = Type.TIsType

  def unit: Unit -> String = _ => ""

  def multiply: ((String, String)) -> String = (a, b) => a + b
}
```

Test classes: `SemilatticeSpec("Furthest", Furthest)` and `SemilatticeSpec("Concat", Concat)`. `Furthest` is a
semilattice on the positions ≥ −1 only; a generator of all integers finds the failure of `leftUnit` at smaller
numbers, which is the invariant that `Expected.Furthest` documents. The two rows that fail for `Concat` are in
`docs/law-status.md` under "String concatenation".

## Chapter 17. Promonads and Freyd categories

### Exercise 17.1: a writer whose effects commute

```scala unit=Exercise1
import parrot.category.*
import Category.Type

/** Integers under addition: commutative, not idempotent. */
object Sum extends CommutativeMonoid(Total.Products) {
  type Self = Int

  def evidence: Int is Type = Type.TIsType

  def unit: Unit -> Int = _ => 0

  def multiply: ((Int, Int)) -> Int = (a, b) => a + b
}

object Counting         extends Writer(Sum)
object CountingKleisli  extends Kleisli(Counting)
object CountingParallel extends Kleisli.ProductStrength(CountingKleisli)

/** Counting arrows side by side: `interchange` holds, because the counts are added in either order. */
val CountingFreyd = Freyd(CountingParallel)
```

Test class: a `FreydSpec` for `CountingFreyd` with `law("interchange") { forAll(interchange)(holds => holds) }`,
as `OptionKleisliProductIsFreydTest` has it. The sentence of section 17.5 under test: interchange holds for all
arrows exactly when the monoid is commutative.

## Chapter 18. Partiality: restriction categories

### Exercise 18.1: a restriction that keeps the output

```scala unit=Exercise1
import parrot.category.*
import Category.Type

object Max extends Semilattice(Total.Products) {
  type Self = Int

  def evidence: Int is Type = Type.TIsType

  def unit: Unit -> Int = _ => Int.MinValue

  def multiply: ((Int, Int)) -> Int = (a, b) => a.max(b)
}

object MaxWriter      extends Writer(Max)
object MaxOutcome     extends OptionT(MaxWriter)
object MaxKleisli     extends Kleisli(MaxOutcome)
object MaxClassical   extends OptionT.ClassicalOf(MaxOutcome)

/** The restriction of an arrow keeps what the arrow outputs. */
object MaxDomains extends Kleisli.ClassicalOf(MaxKleisli, MaxClassical)
```

Prediction: R1, R3 and R4 hold, because the output of the test is combined with the same output again and the
maximum is idempotent. R2 fails: where one of two tests fails, the test after it does not run, so the two orders
output different numbers. `RestrictionSpec` shows it; the tests of the library have this instance as
`MaxOutcomeRestrictionTest`.

## Chapter 19. Iteration and recursion on promonads

### Exercise 19.1: the trace of the while loop, by hand

```scala unit=Exercise1
import parrot.category.*
import Category.Type

/** Feedback in 𝒫 through tagged unions, written as a loop: enter on the left, run until an exit on the left. */
object HandFeedback extends Traced(Freyd(Partial.Choice)) {

  def trace[A: Type, B: Type, U: Type](p: Either[A, U] ~> Either[B, U]): A ~> B = {
    @annotation.tailrec
    def loop(x: Either[A, U]): B = {
      p.run(x) match {
        case Left(b)  => b
        case Right(u) => loop(Right(u))
      }
    }
    Partial(a => loop(Left(a)))
  }
}
```

Test class: a `TracedSpec` for `HandFeedback`, with the generators of `PartialFeedbackIsTracedTest`. It agrees with
`Partial.Feedback`, which is `Traced.OfElgot(Partial.Loops)`.

## Chapter 20. Case study: parser combinators

### Exercise 20.1: a derived combinator with its law

```scala unit=Exercise1
import parrot.category.*
import parrot.parser.*

/** Items separated by a separator, with an optional separator at the end. */
final class SeparatedEnded(tracked val algebra: ParserAlgebra) {
  import algebra.*

  def separatedEndedBy[A, B, C](p: P[A, B], separator: P[A, C]): P[A, Vector[B]] = {
    p.separatedBy(separator) <* separator.optional
  }

  /** *separatedEndedBy*(*p*,*s*) = *separatedBy*(*p*,*s*) followed by an optional *s*, whose result is dropped */
  def separatedEndedByDefinition[A, B, C](p: P[A, B], separator: P[A, C])(
    using P[A, Vector[B]] is Observable
  ): Boolean = {
    separatedEndedBy(p, separator) =?= thenSkip(separatedBy(p, separator), optional(separator))
  }
}
```

Run it on both interpreters: `SeparatedEnded(StrictParser())` and `SeparatedEnded(ReferenceParser())`, with the
observations of `ParserGen.exact`, as `ParserLawSpec` does for `atLeastOnceDefinition`.
