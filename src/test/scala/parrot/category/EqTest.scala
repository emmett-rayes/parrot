package parrot
package category

import org.scalacheck.Gen

import Sample.given

/** The laws of [[Eq]]: an equivalence relation. Pairs and triples are sampled so that equal values occur often. */
abstract class EqSpec[A: Sample](using typename: TypeName[A]) extends LawSuite("Eq", typename.name) {
  import A.eq.EqLaws.*
  private val pairs: Gen[(A, A)] = Gen.oneOf(Gen.zip(A.gen, A.gen), A.gen.map(a => (a, a)))

  law("reflexivity") {
    forAll(A.gen)(a => reflexivity(a))
  }

  law("symmetry") {
    forAll(pairs)((a, b) => symmetry(a, b))
  }

  law("transitivity") {
    forAll(pairs, Gen.oneOf(true, false)) { case ((a, b), same) =>
      transitivity(a, b, if same then b else a)
    }
  }
}

class IntIsEqTest    extends EqSpec[Int]
class DoubleIsEqTest extends EqSpec[Double]
class StringIsEqTest extends EqSpec[String]
class OptionIsEqTest extends EqSpec[Option[Int]]
class Tuple2IsEqTest extends EqSpec[(Int, String)]
class EitherIsEqTest extends EqSpec[Either[Int, String]]
class ListIsEqTest   extends EqSpec[List[Int]]
class VectorIsEqTest extends EqSpec[Vector[Int]]
