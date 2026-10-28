package parrot
package parser

import category.*
import org.scalacheck.Gen

import Sample.given

// ==== ReferenceParser ====

class ReferenceIsCategoryTest extends CategorySpec(ReferenceFixture.category)

class ReferenceIsPromonadTest extends PromonadSpec(ReferenceFixture)

class ReferenceIsRestrictionTest
    extends RestrictionSpec("ReferenceParser", ReferenceFixture, Interpreters.reference.Choice)

class ReferenceIsClassicalTest extends ClassicalSpec("ReferenceParser", ReferenceFixture, Interpreters.reference.Choice)

class ReferenceZippingIsStrongTest
    extends StrongSpec("ReferenceParser (zipping)", ReferenceFixture, Interpreters.reference.Zipping) {
  also("Freyd") {
    counterexample("interchange", "consuming input is not commutative") {
      forAll(interchange)(holds => holds)
    }
  }
}

class ReferenceBranchingIsStrongTest
    extends StrongSpec("ReferenceParser (branching)", ReferenceFixture, Interpreters.reference.Branching) {
  also("Freyd") {
    law("interchange", "holds: only one side runs") {
      forAll(interchange)(holds => holds)
    }
  }
}

class ReferenceLoopsIsElgotTest
    extends ElgotSpec("ReferenceParser (guarded)", ReferenceFixture, Interpreters.reference.Loops) {
  import PF.P.P
  def step[A: Sample]: Gen[P[Int, Either[A, Int]]]               = ParserSteps.step[A](Interpreters.reference)
  def step2[A: Sample]: Gen[P[Int, Either[Either[A, Int], Int]]] = ParserSteps.step2[A](Interpreters.reference)
  def shrink: Int -> Int                                         = _ / 2
  def bijection: (Int -> Int, Int -> Int)                        = (x => -x, x => -x)
}

class ReferenceKnotsIsRecursionTest
    extends RecursionSpec("ReferenceParser (guarded)", ReferenceFixture, Interpreters.reference.Knots) {
  import PF.P.P
  def guarded[B: Sample]: Gen[P[Int, B] -> P[Int, B]] = ParserSteps.rules[B](Interpreters.reference)

  counterexample("fixedPoint", "for left-recursive rules: the call fails") {
    val observations = PF.observe[Int, Int]
    forAll(observations, Grammars.terms) { (o, term) =>
      given (P[Int, Int] is Observable) = o
      R.RecursionLaws.fixedPoint(ParserSteps.leftRecursive(Interpreters.reference)(term))
    }
  }
}

class ReferenceIsObservableTest extends ObservableSpec(ReferenceFixture.category)

class ReferenceDiagnosticsIsObservableTest extends ObservableSpec(ReferenceDiagnosticsFixture)

class ReferenceIsPreorderTest
    extends PreorderSpec(
      "ReferenceParser",
      ParserGen.arrow[Int, Int](Interpreters.reference),
      ParserGen.variant[Int, Int](Interpreters.reference),
      ParserGen.refine[Int, Int](Interpreters.reference),
      ParserGen.oracles[Int, Int](Interpreters.reference),
    )

// ==== StrictParser ====

class StrictIsCategoryTest extends CategorySpec(StrictFixture.category)

class StrictIsPromonadTest extends PromonadSpec(StrictFixture)

class StrictIsRestrictionTest extends RestrictionSpec("StrictParser", StrictFixture, Interpreters.strict.Choice)

class StrictIsClassicalTest extends ClassicalSpec("StrictParser", StrictFixture, Interpreters.strict.Choice)

class StrictZippingIsStrongTest
    extends StrongSpec("StrictParser (zipping)", StrictFixture, Interpreters.strict.Zipping) {
  also("Freyd") {
    counterexample("interchange", "consuming input is not commutative") {
      forAll(interchange)(holds => holds)
    }
  }
}

class StrictBranchingIsStrongTest
    extends StrongSpec("StrictParser (branching)", StrictFixture, Interpreters.strict.Branching) {
  also("Freyd") {
    law("interchange", "holds: only one side runs") {
      forAll(interchange)(holds => holds)
    }
  }
}

class StrictLoopsIsElgotTest extends ElgotSpec("StrictParser (guarded)", StrictFixture, Interpreters.strict.Loops) {
  import PF.P.P
  def step[A: Sample]: Gen[P[Int, Either[A, Int]]]               = ParserSteps.step[A](Interpreters.strict)
  def step2[A: Sample]: Gen[P[Int, Either[Either[A, Int], Int]]] = ParserSteps.step2[A](Interpreters.strict)
  def shrink: Fn[Int, Int]                                       = Fn.lift(_ / 2)
  def bijection: (Fn[Int, Int], Fn[Int, Int])                    = (Fn.lift(x => -x), Fn.lift(x => -x))
}

class StrictKnotsIsRecursionTest
    extends RecursionSpec("StrictParser (guarded)", StrictFixture, Interpreters.strict.Knots) {
  import PF.P.P
  def guarded[B: Sample]: Gen[P[Int, B] -> P[Int, B]] = ParserSteps.rules[B](Interpreters.strict)

  counterexample("fixedPoint", "for left-recursive rules: seed growing") {
    val observations = PF.observe[Int, Int]
    forAll(observations, Grammars.terms) { (o, term) =>
      given (P[Int, Int] is Observable) = o
      R.RecursionLaws.fixedPoint(ParserSteps.leftRecursive(Interpreters.strict)(term))
    }
  }
}

class StrictIsObservableTest extends ObservableSpec(StrictFixture.category)

class StrictDiagnosticsIsObservableTest extends ObservableSpec(StrictDiagnosticsFixture)

class StrictIsPreorderTest
    extends PreorderSpec(
      "StrictParser",
      ParserGen.arrow[Int, Int](Interpreters.strict),
      ParserGen.variant[Int, Int](Interpreters.strict),
      ParserGen.refine[Int, Int](Interpreters.strict),
      ParserGen.oracles[Int, Int](Interpreters.strict),
    )

class FnsIsObservableTest extends ObservableSpec(FnsFixture)

// ==== Diagnostics ====

class ExpectedIsPreorderTest
    extends PreorderSpec[Expected](
      "Expected (furthest)",
      ParserGen.expected,
      e => Expected(e.position, e.expectations.toList.reverse.toSet),
      (e, x) => Expected.Furthest.multiply((e, x)),
      Gen.const((Observable[Expected], Expected.ExpectedIsPreorder)),
    )

/** Guarded steps and rules for the iteration and recursion specs, and a left-recursive rule. */
object ParserSteps {

  /** Steps that consume "a" before continuing. */
  def step[A: Sample](alg: ParserAlgebra): Gen[alg.P[Int, Either[A, Int]]] = {
    import alg.*
    for {
      term <- Grammars.terms
      stop <- Sample.function[Int, A]
      next <- Sample.function[Int, Int]
    } yield Grammars.consume(alg)("a").map(lift[Int, Either[A, Int]](n => Right(next(n)))) |>
      Grammars.interpret(alg)(term).map(lift[Int, Either[A, Int]](n => Left(stop(n))))
  }

  /** Steps with two ways to continue, both after consuming input. */
  def step2[A: Sample](alg: ParserAlgebra): Gen[alg.P[Int, Either[Either[A, Int], Int]]] = {
    import alg.*
    for {
      term  <- Grammars.terms
      stop  <- Sample.function[Int, A]
      next  <- Sample.function[Int, Int]
      outer <- Sample.function[Int, Int]
    } yield Grammars.consume(alg)("a").map(lift[Int, Either[Either[A, Int], Int]](n => Right(next(n)))) |>
      Grammars.consume(alg)("b").map(lift[Int, Either[Either[A, Int], Int]](n => Left(Right(outer(n))))) |>
      Grammars.interpret(alg)(term).map(lift[Int, Either[Either[A, Int], Int]](n => Left(Left(stop(n)))))
  }

  /** Rules that call themselves only between parentheses. */
  def rules[B: Sample](alg: ParserAlgebra): Gen[alg.P[Int, B] -> alg.P[Int, B]] = {
    import alg.*
    for {
      term <- Grammars.terms
      out  <- Sample.function[Int, B]
    } yield (rec: P[Int, B]) =>
      Grammars.interpret(alg)(term).map(lift(out)) |> (Grammars.consume(alg)("(") *> rec <* Grammars.consume(alg)(")"))
  }

  /** A left-recursive rule: *rule* = *rule* "a" | *term*. */
  def leftRecursive(alg: ParserAlgebra)(term: Term): alg.P[Int, Int] -> alg.P[Int, Int] = {
    import alg.*
    rec => (rec <* Grammars.consume(alg)("a")).map(lift(_ + 1)) |> Grammars.interpret(alg)(term)
  }
}
