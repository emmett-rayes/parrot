package parrot
package category

import Sample.given
import Category.Type

/** The laws of [[RestrictionProducts]], for structures on a category whose objects are all types. */
abstract class RestrictionProductsSpec(
  name: String,
  tracked val products: RestrictionProducts.On[Restriction.On[Category { type Obj = Type }]],
  structure: String = "RestrictionProducts",
)(using
  category: CategoryFixture.For[products.restriction.category.type],
  types: SampleTypes,
  tensor: [X, Y] => (Sample[X], Sample[Y]) ?-> Sample[products.monoidal.Tensor[X, Y]],
) extends LawSuite(structure, name) {
  import types.{T1, T2, T3, given}
  import category.*
  import products.monoidal.`*`
  import products.restriction.category.-->
  import products.RestrictionProductsLaws.*

  private given TensorSample: [X: Sample, Y: Sample] => Sample[products.monoidal.Tensor[X, Y]] = tensor[X, Y]

  also("RestrictionProducts") {
    law("fstPair") {
      val observations = observe[T1, T2]
      val fs           = arrow[T1, T2]
      val gs           = arrow[T1, T3]

      forAll(observations, fs, gs) { (observe, f, g) =>
        given ((T1 --> T2) is Observable) = observe
        fstPair(f, g)
      }
    }

    law("sndPair") {
      val observations = observe[T1, T3]
      val fs           = arrow[T1, T2]
      val gs           = arrow[T1, T3]

      forAll(observations, fs, gs) { (observe, f, g) =>
        given ((T1 --> T3) is Observable) = observe
        sndPair(f, g)
      }
    }

    law("pairRestriction") {
      val observations = observe[T1, T1]
      val fs           = arrow[T1, T2]
      val gs           = arrow[T1, T3]

      forAll(observations, fs, gs) { (observe, f, g) =>
        given ((T1 --> T1) is Observable) = observe
        pairRestriction(f, g)
      }
    }

    law("projectionsTotal") {
      val observations = observe[T2 * T3, T2 * T3]

      forAll(observations) { observe =>
        given (((T2 * T3) --> (T2 * T3)) is Observable) = observe
        projectionsTotal[T2, T3]
      }
    }

    law("pairUniqueness") {
      val observations = observe[T1, T2 * T3]
      val hs           = arrow[T1, T2 * T3]

      forAll(observations, hs) { (observe, h) =>
        given ((T1 --> (T2 * T3)) is Observable) = observe
        pairUniqueness[T1, T2, T3](h)
      }
    }

    law("pairCongruence") {
      val observations = observe[T1, T2 * T3]
      val fs           = arrow[T1, T2]
      val gs           = arrow[T1, T3]

      forAll(observations, fs, gs) { (observe, f, g) =>
        given ((T1 --> (T2 * T3)) is Observable) = observe
        pairCongruence(f, variant(f), g, variant(g))
      }
    }
  }
}

// ==== 𝒫 ====

class PartialIsRestrictionProductsTest extends RestrictionProductsSpec("Partial", Partial.RestrictionProducts)

// ==== Functions that may fail ====

/** Pairs as a bifunctor on functions that may fail: *f* × *g* fails where *f* or *g* does. */
object OptionPairsIsBifunctor extends Endobifunctor(Kleisli.OptionKleisli.arrows) {
  type Self = Tuple2

  def objects[A: Type, B: Type]: (A, B) is Type = {
    Type.TIsType
  }

  def bimap[A1: Type, A2: Type, B1: Type, B2: Type](f: A1 -> Option[B1], g: A2 -> Option[B2])
    : ((A1, A2)) -> Option[(B1, B2)] = {
    (a, b) => f(a).flatMap(x => g(b).map(y => (x, y)))
  }
}

/** Pairs on functions that may fail: a symmetric monoidal structure, since failure is a commutative effect. */
object OptionPairs
    extends Symmetric(Kleisli.OptionKleisli.arrows, Kleisli.OptionKleisli.arrows.Object[Unit], OptionPairsIsBifunctor) {
  import category.{Iso, <->}

  def braid[A: Type, B: Type]: ((A, B)) -> Option[(B, A)] = {
    (a, b) => Some((b, a))
  }

  def leftUnitor[A: Type]: (Unit, A) <-> A = {
    Iso(p => Some(p._2), a => Some(((), a)))
  }

  def associator[A: Type, B: Type, C: Type]: ((A, B), C) <-> (A, (B, C)) = {
    Iso({ case ((a, b), c) => Some((a, (b, c))) }, { case (a, (b, c)) => Some(((a, b), c)) })
  }
}

/** The restriction products of functions that may fail: pairs, with a pairing that fails where a component does. */
object OptionRestrictionProducts extends RestrictionProducts(Kleisli.OptionDomains, OptionPairs) {

  def fst[A: Type, B: Type]: ((A, B)) -> Option[A] = {
    p => Some(p._1)
  }

  def snd[A: Type, B: Type]: ((A, B)) -> Option[B] = {
    p => Some(p._2)
  }

  def pair[X: Type, A: Type, B: Type](f: X -> Option[A], g: X -> Option[B]): X -> Option[(A, B)] = {
    x => f(x).flatMap(a => g(x).map(b => (a, b)))
  }
}

class OptionPairsIsSymmetricTest extends SymmetricSpec(OptionPairs)(using typename = TypeName("Tuple2"))

class OptionKleisliIsRestrictionProductsTest
    extends RestrictionProductsSpec("Kleisli[Option]", OptionRestrictionProducts) {
  import Kleisli.OptionKleisli.arrows.>>>

  also("Products") {
    counterexample("fstPair", "π₁ ∘ ⟨f,g⟩ = f fails where g does: the pairs are not products") {
      val observations = OptionKleisliFixture.observe[Int, String]
      val fs           = OptionKleisliFixture.arrow[Int, String]
      val gs           = OptionKleisliFixture.arrow[Int, Boolean]

      forAll(observations, fs, gs) { (observe, f, g) =>
        given ((Int -> Option[String]) is Observable) = observe
        (OptionRestrictionProducts.pair(f, g) >>> OptionRestrictionProducts.fst[String, Boolean]) =?= f
      }
    }
  }
}
