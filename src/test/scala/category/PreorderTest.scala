package parrot
package category

import org.scalacheck.Gen

/** The laws of [[Preorder]], for orders drawn afresh for every case, each with an [[Observable]] that makes the same
  * observations. `refine` builds a value above its first argument, so that ordered pairs and chains occur often.
  */
abstract class PreorderSpec[A](
  name: String,
  values: Gen[A],
  variant: A -> A,
  refine: (A, A) -> A,
  oracles: Gen[(A is Observable, A is Preorder)],
) extends LawSuite("Preorder", name) {

  private lazy val pairs: Gen[(A, A)] = {
    Gen.oneOf(
      Gen.zip(values, values),
      values.map(a => (a, variant(a))),
      Gen.zip(values, values).map((a, x) => (a, refine(a, x))),
    )
  }

  law("reflexivity") {
    forAll(oracles, values) { case ((_, o), a) => o.PreorderLaws.reflexivity(a) }
  }

  law("transitivity") {
    forAll(oracles, values, values, values) { case ((_, o), a, x, y) =>
      val b = refine(a, x)
      o.PreorderLaws.transitivity(a, b, refine(b, y))
    }
  }

  law("soundness") {
    forAll(oracles, values) { case ((_, o), a) => o.PreorderLaws.soundness(a, variant(a)) }
  }

  law("agreement") {
    forAll(oracles, pairs) { case ((e, o), (a, b)) => o.PreorderLaws.agreement(a, b)(using e) }
  }
}

class IntMaxIsPreorderTest
    extends PreorderSpec[Int](
      "Int maximum",
      Sample.IntSample.gen,
      a => a,
      (a, x) => IntMax.multiply((a, x)),
      Gen.const((Observable[Int], Preorder.of(IntMax))),
    )

class BooleanOrIsPreorderTest
    extends PreorderSpec[Boolean](
      "Boolean disjunction",
      Sample.BooleanSample.gen,
      a => a,
      (a, x) => BooleanOr.multiply((a, x)),
      Gen.const((Observable[Boolean], Preorder.of(BooleanOr))),
    )
