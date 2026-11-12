package parrot
package category

import Sample.given
import Category.{Discrete2, Type}
import Product.{Discrete2Diagram, PairCone}

/** The laws of [[Cone]], for cones over a diagram of shape **2** in a category whose objects are all types. */
abstract class ConeSpec(
  name: String,
  tracked val cone: Cone {
    val diagram: Functor { val source: Discrete2.type; val target: Category { type Obj = Type } }
  },
  structure: String = "Cone",
)(using
  category: CategoryFixture.For[cone.diagram.target.type],
  apex: Sample[cone.X],
  first: Sample[cone.diagram.F[0]],
  second: Sample[cone.diagram.F[1]],
) extends LawSuite(structure, name) {
  import category.*
  import cone.X
  import cone.diagram.F as D
  import cone.diagram.target.-->
  import cone.ConeLaws.*

  also("Cone") {
    law("commutes", "at the identities, the only morphisms of the shape") {
      val observations1 = observe[X, D[0]]
      val observations2 = observe[X, D[1]]

      forAll(observations1, observations2) { (observe1, observe2) =>
        given O1: ((X --> D[0]) is Observable) = observe1
        given O2: ((X --> D[1]) is Observable) = observe2
        commutes[0, 0](Discrete2.identity[0]) && commutes[1, 1](Discrete2.identity[1])
      }
    }
  }
}

/** The laws of [[Limit]], for limits of a diagram of shape **2** in a category whose objects are all types. */
abstract class LimitSpec(
  name: String,
  tracked override val cone: Limit {
    val diagram: Functor { val source: Discrete2.type; val target: Category { type Obj = Type } }
  },
  structure: String = "Limit",
)(using
  category: CategoryFixture.For[cone.diagram.target.type],
  types: SampleTypes,
  apex: Sample[cone.X],
  first: Sample[cone.diagram.F[0]],
  second: Sample[cone.diagram.F[1]],
) extends ConeSpec(name, cone, structure) {
  import types.{T1, given}
  import category.*
  import cone.X
  import cone.diagram.F as D
  import cone.diagram.target.-->
  import cone.LimitLaws.*

  also("Limit") {
    law("universal") {
      val observations1 = observe[T1, D[0]]
      val observations2 = observe[T1, D[1]]
      val fs            = arrow[T1, D[0]]
      val gs            = arrow[T1, D[1]]

      forAll(observations1, observations2, fs, gs) { (observe1, observe2, f, g) =>
        given O1: ((T1 --> D[0]) is Observable) = observe1
        given O2: ((T1 --> D[1]) is Observable) = observe2
        val pair = PairCone(cone.diagram, cone.diagram.target.Object[T1])(f, g)
        universal[0](pair) && universal[1](pair)
      }
    }

    law("uniqueness") {
      val observations = observe[T1, X]
      val hs           = arrow[T1, X]

      forAll(observations, hs) { (observe, h) =>
        given ((T1 --> X) is Observable) = observe
        uniqueness(h)
      }
    }

    law("factorCongruence") {
      val observations = observe[T1, X]
      val fs           = arrow[T1, D[0]]
      val gs           = arrow[T1, D[1]]

      forAll(observations, fs, gs) { (observe, f, g) =>
        given ((T1 --> X) is Observable) = observe
        val apex = cone.diagram.target.Object[T1]
        factorCongruence(PairCone(cone.diagram, apex)(f, g), PairCone(cone.diagram, apex)(variant(f), variant(g)))
      }
    }
  }
}

// ==== 𝒮 ====

class PairConeIsConeTest extends ConeSpec("PairCone on Total", IntStringLimits.cone)

class TotalLimitOfIsLimitTest
    extends LimitSpec("LimitOf on Total", IntStringLimits.byAbstraction)(
      using apex = LimitSamples.apex(IntStringLimits.byAbstraction)
    )

class TotalLimitsIsLimitTest
    extends LimitSpec("Limits on Total", IntStringLimits.amongAll)(
      using apex = LimitSamples.apex(IntStringLimits.amongAll)
    )

class TotalDiscreteLimitOfIsLimitTest
    extends LimitSpec("DiscreteLimitOf on Total", IntStringLimits.discrete)(
      using apex = LimitSamples.apex(IntStringLimits.discrete)
    )

class Tuple2AsLimitIsLimitTest extends LimitSpec("Tuple2 on Total (as a limit)", IntStringLimits.pairs)
