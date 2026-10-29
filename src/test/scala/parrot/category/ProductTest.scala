package parrot
package category

import Sample.given

/** The laws of [[Category.Product]], for the product 𝒮 × 𝒫 of the two categories of programs. */
class ProductIsCategoryTest extends LawSuite("Category", "Total × Partial") {
  private val K = Category.Product(Total, Partial)
  import K.given
  import K.CategoryLaws.*

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
