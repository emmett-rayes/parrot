package parrot
package category

import Sample.given
import Category.{Discrete2, Type}
import Coproduct.CopairCocone

/** The laws of [[Cocone]], for cocones under a diagram of shape **2** in a category whose objects are all types. */
abstract class CoconeSpec(
  name: String,
  tracked val cocone: Cocone {
    val diagram: Functor { val source: Discrete2.type; val target: Category { type Obj = Type } }
  },
  structure: String = "Cocone",
)(using
  category: CategoryFixture.For[cocone.diagram.target.type],
  apex: Sample[cocone.X],
  first: Sample[cocone.diagram.F[0]],
  second: Sample[cocone.diagram.F[1]],
) extends LawSuite(structure, name) {
  import category.*
  import cocone.X
  import cocone.diagram.F as D
  import cocone.diagram.target.-->
  import cocone.CoconeLaws.*

  also("Cocone") {
    law("commutes", "at the identities, the only morphisms of the shape") {
      val observations1 = observe[D[0], X]
      val observations2 = observe[D[1], X]

      forAll(observations1, observations2) { (observe1, observe2) =>
        given O1: ((D[0] --> X) is Observable) = observe1
        given O2: ((D[1] --> X) is Observable) = observe2
        commutes[0, 0](Discrete2.identity[0]) && commutes[1, 1](Discrete2.identity[1])
      }
    }
  }
}

/** The laws of [[Colimit]], for colimits of a diagram of shape **2** in a category whose objects are all types. */
abstract class ColimitSpec(
  name: String,
  tracked override val cocone: Colimit {
    val diagram: Functor { val source: Discrete2.type; val target: Category { type Obj = Type } }
  },
  structure: String = "Colimit",
)(using
  category: CategoryFixture.For[cocone.diagram.target.type],
  types: SampleTypes,
  apex: Sample[cocone.X],
  first: Sample[cocone.diagram.F[0]],
  second: Sample[cocone.diagram.F[1]],
) extends CoconeSpec(name, cocone, structure) {
  import types.{T1, given}
  import category.*
  import cocone.X
  import cocone.diagram.F as D
  import cocone.diagram.target.-->
  import cocone.ColimitLaws.*

  also("Colimit") {
    law("universal") {
      val observations1 = observe[D[0], T1]
      val observations2 = observe[D[1], T1]
      val fs            = arrow[D[0], T1]
      val gs            = arrow[D[1], T1]

      forAll(observations1, observations2, fs, gs) { (observe1, observe2, f, g) =>
        given O1: ((D[0] --> T1) is Observable) = observe1
        given O2: ((D[1] --> T1) is Observable) = observe2
        val copair = CopairCocone(cocone.diagram, cocone.diagram.target.Object[T1])(f, g)
        universal[0](copair) && universal[1](copair)
      }
    }

    law("uniqueness") {
      val observations = observe[X, T1]
      val hs           = arrow[X, T1]

      forAll(observations, hs) { (observe, h) =>
        given ((X --> T1) is Observable) = observe
        uniqueness(h)
      }
    }

    law("factorCongruence") {
      val observations = observe[X, T1]
      val fs           = arrow[D[0], T1]
      val gs           = arrow[D[1], T1]

      forAll(observations, fs, gs) { (observe, f, g) =>
        given ((X --> T1) is Observable) = observe
        val apex = cocone.diagram.target.Object[T1]
        factorCongruence(CopairCocone(cocone.diagram, apex)(f, g), CopairCocone(cocone.diagram, apex)(variant(f), variant(g)))
      }
    }
  }
}

// ==== 𝒮 ====

class CopairCoconeIsCoconeTest extends CoconeSpec("CopairCocone on Total", IntStringColimits.cocone)

class TotalColimitOfIsColimitTest
    extends ColimitSpec("ColimitOf on Total", IntStringColimits.byAbstraction)(
      using apex = ColimitSamples.apex(IntStringColimits.byAbstraction)
    )

class TotalColimitsIsColimitTest
    extends ColimitSpec("Colimits on Total", IntStringColimits.amongAll)(
      using apex = ColimitSamples.apex(IntStringColimits.amongAll)
    )

class TotalDiscreteColimitOfIsColimitTest
    extends ColimitSpec("DiscreteColimitOf on Total", IntStringColimits.discrete)(
      using apex = ColimitSamples.apex(IntStringColimits.discrete)
    )

class EitherAsColimitIsColimitTest extends ColimitSpec("Either on Total (as a colimit)", IntStringColimits.unions)
