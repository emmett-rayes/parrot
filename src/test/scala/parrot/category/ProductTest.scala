package parrot
package category

import Category.Type
import LimitProducts.FName
import Sample.given

/** The laws of [[Category.Product]], for the product 𝒮 × 𝒫 of the two categories of programs. */
class ProductIsCategoryTest extends LawSuite("Category", "Total × Partial") {
  private val category = Category.Product(Total, Partial)
  import category.given
  import category.CategoryLaws.*

  law("leftIdentity") {
    val observations1 = TotalFixture.observe[Int, String]
    val observations2 = PartialFixture.observe[Long, Boolean]
    val fs            = TotalFixture.arrow[Int, String]
    val gs            = PartialFixture.arrow[Long, Boolean]

    forAll(observations1, observations2, fs, gs) { (o1, o2, f, g) =>
      given ((Int -> String, Long ~> Boolean) is Observable) = Observable.Tuple2IsObservable(using o1, o2)
      leftIdentity[(Int, Long), (String, Boolean)]((f, g))
    }
  }

  law("rightIdentity") {
    val observations1 = TotalFixture.observe[Int, String]
    val observations2 = PartialFixture.observe[Long, Boolean]
    val fs            = TotalFixture.arrow[Int, String]
    val gs            = PartialFixture.arrow[Long, Boolean]

    forAll(observations1, observations2, fs, gs) { (o1, o2, f, g) =>
      given ((Int -> String, Long ~> Boolean) is Observable) = Observable.Tuple2IsObservable(using o1, o2)
      rightIdentity[(Int, Long), (String, Boolean)]((f, g))
    }
  }

  law("associativity") {
    forAll(
      org.scalacheck.Gen.zip(TotalFixture.observe[Int, Long], PartialFixture.observe[Int, Long]),
      org.scalacheck.Gen.zip(TotalFixture.arrow[Int, String], PartialFixture.arrow[Int, String]),
      org.scalacheck.Gen.zip(TotalFixture.arrow[String, Boolean], PartialFixture.arrow[String, Boolean]),
      org.scalacheck.Gen.zip(TotalFixture.arrow[Boolean, Long], PartialFixture.arrow[Boolean, Long]),
    ) { (o, f, g, h) =>
      given ((Int -> Long, Int ~> Long) is Observable) = Observable.Tuple2IsObservable(using o._1, o._2)
      associativity[(Int, Int), (String, String), (Boolean, Boolean), (Long, Long)](f, g, h)
    }
  }

  law("congruence") {
    forAll(
      org.scalacheck.Gen.zip(TotalFixture.observe[Int, Boolean], PartialFixture.observe[Int, Boolean]),
      org.scalacheck.Gen.zip(TotalFixture.arrow[Int, String], PartialFixture.arrow[Int, String]),
      org.scalacheck.Gen.zip(TotalFixture.arrow[String, Boolean], PartialFixture.arrow[String, Boolean]),
    ) { (o, f, g) =>
      given ((Int -> Boolean, Int ~> Boolean) is Observable) = Observable.Tuple2IsObservable(using o._1, o._2)
      val f2 = (TotalFixture.variant(f._1), PartialFixture.variant(f._2))
      val g2 = (TotalFixture.variant(g._1), PartialFixture.variant(g._2))
      congruence[(Int, Int), (String, String), (Boolean, Boolean)](f, f2, g, g2)
    }
  }
}

/** The laws of [[Products]], for binary products on a category whose objects are all types. */
abstract class ProductsSpec(
  tracked override val category: Category { type Obj = Type },
  tracked override val bifunctor: Products.On[category.type],
)(using
  fixture: CategoryFixture.For[category.type],
  typename: TypeName[bifunctor.Self],
  types: SampleTypes,
  sample: [X, Y] => (Sample[X], Sample[Y]) ?-> Sample[bifunctor.F[X, Y]],
) extends BifunctorSpec(category, bifunctor, "Products") {
  import types.{T1, T2, T3, T4, given}
  import fixture.*
  import category.-->
  import bifunctor.F
  import bifunctor.ProductsLaws.*

  private given BSample: [X: Sample, Y: Sample] => Sample[F[X, Y]] = sample[X, Y]

  also("Products") {
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

    law("pairUniqueness") {
      val observations = observe[T1, F[T2, T3]]
      val hs           = arrow[T1, F[T2, T3]]

      forAll(observations, hs) { (observe, h) =>
        given ((T1 --> F[T2, T3]) is Observable) = observe
        pairUniqueness[T1, T2, T3](h)
      }
    }

    law("pairCongruence") {
      val observations = observe[T1, F[T2, T3]]
      val fs           = arrow[T1, T2]
      val gs           = arrow[T1, T3]

      forAll(observations, fs, gs) { (observe, f, g) =>
        given ((T1 --> F[T2, T3]) is Observable) = observe
        pairCongruence(f, variant(f), g, variant(g))
      }
    }

    law("bimapIsPairing") {
      val observations = observe[F[T1, T2], F[T4, T3]]
      val fs           = arrow[T1, T4]
      val gs           = arrow[T2, T3]

      forAll(observations, fs, gs) { (observe, f, g) =>
        given ((F[T1, T2] --> F[T4, T3]) is Observable) = observe
        bimapIsPairing(f, g)
      }
    }
  }
}

class ScalaTuple2IsProductsTest   extends ProductsSpec(Total, Total.Tuple2IsProducts)
class TotalLimitIsProductsTest    extends ProductsSpec(Total, LimitProducts)
class ScalaEitherOpIsProductsTest extends ProductsSpec(Total.op, Total.EitherIsCoproducts.op)
