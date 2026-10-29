package parrot
package category

import org.scalacheck.Gen

/** The laws of [[Monoidal]] and [[Symmetric]], for structures on a category whose objects are all types. */
abstract class SymmetricSpec(tracked val M: Symmetric { val K: Category { type Obj = Type } })(using
  F: CategoryFixture.On[M.K.type],
  monoidal: TypeName[M.type],
  category: TypeName[M.K.type],
  types: SampleTypes,
  tensor: [X, Y] => (Sample[X], Sample[Y]) ?=> Sample[M.Tensor[X, Y]],
  unit: Sample[M.I],
) extends LawSuite("Symmetric", s"${monoidal.name} on ${category.name}") {
  import types.{T1, T2, T3, T4, given}
  import F.*
  import M.K.-->
  import M.SymmetricLaws.*

  private given TensorSample: [X: Sample, Y: Sample] => Sample[M.Tensor[X, Y]] = tensor[X, Y]

  private type T[X, Y] = M.Tensor[X, Y]
  private type I       = M.I

  also("Monoidal") {
    import M.MonoidalLaws.*

    law("isomorphisms") {
      forAll(
        Gen.zip(observe[T[I, T1], T[I, T1]], observe[T1, T1], observe[T[T1, I], T[T1, I]]),
        Gen.zip(
          observe[T[T[T1, T2], T4], T[T[T1, T2], T4]],
          observe[T[T1, T[T2, T4]], T[T1, T[T2, T4]]],
        ),
      ) { case ((o1, o2, o3), (o4, o5)) =>
        given O1: ((T[I, T1] --> T[I, T1]) is Observable)                 = o1
        given O2: ((T1 --> T1) is Observable)                             = o2
        given O3: ((T[T1, I] --> T[T1, I]) is Observable)                 = o3
        given O4: ((T[T[T1, T2], T4] --> T[T[T1, T2], T4]) is Observable) = o4
        given O5: ((T[T1, T[T2, T4]] --> T[T1, T[T2, T4]]) is Observable) = o5
        isomorphisms[T1, T2, T4]
      }
    }

    law("leftUnitorNaturality") {
      val observations = observe[T[I, T1], T2]
      val fs           = arrow[T1, T2]

      forAll(observations, fs) { (observe, f) =>
        given ((T[I, T1] --> T2) is Observable) = observe
        leftUnitorNaturality(f)
      }
    }

    law("rightUnitorNaturality") {
      val observations = observe[T[T1, I], T2]
      val fs           = arrow[T1, T2]

      forAll(observations, fs) { (observe, f) =>
        given ((T[T1, I] --> T2) is Observable) = observe
        rightUnitorNaturality(f)
      }
    }

    law("associatorNaturality") {
      val observations = observe[T[T[T1, T2], T3], T[T4, T[T1, T2]]]
      val fs           = arrow[T1, T4]
      val gs           = arrow[T2, T1]
      val hs           = arrow[T3, T2]

      forAll(observations, fs, gs, hs) { (observe, f, g, h) =>
        given ((T[T[T1, T2], T3] --> T[T4, T[T1, T2]]) is Observable) = observe
        associatorNaturality(f, g, h)
      }
    }

    law("triangle") {
      val observations = observe[T[T[T1, I], T2], T[T1, T2]]

      forAll(observations) { observe =>
        given ((T[T[T1, I], T2] --> T[T1, T2]) is Observable) = observe
        triangle[T1, T2]
      }
    }

    law("pentagon") {
      val observations = observe[T[T[T[T1, T2], T3], T4], T[T1, T[T2, T[T3, T4]]]]

      forAll(observations) { observe =>
        given ((T[T[T[T1, T2], T3], T4] --> T[T1, T[T2, T[T3, T4]]]) is Observable) =
          observe
        pentagon[T1, T2, T3, T4]
      }
    }
  }

  law("braidNaturality") {
    val observations = observe[T[T1, T2], T[T3, T4]]
    val fs           = arrow[T1, T4]
    val gs           = arrow[T2, T3]

    forAll(observations, fs, gs) { (observe, f, g) =>
      given ((T[T1, T2] --> T[T3, T4]) is Observable) = observe
      braidNaturality(f, g)
    }
  }

  law("symmetry") {
    val observations = observe[T[T1, T2], T[T1, T2]]

    forAll(observations) { observe =>
      given ((T[T1, T2] --> T[T1, T2]) is Observable) = observe
      symmetry[T1, T2]
    }
  }

  law("hexagon") {
    val observations = observe[T[T[T1, T2], T4], T[T2, T[T4, T1]]]

    forAll(observations) { observe =>
      given ((T[T[T1, T2], T4] --> T[T2, T[T4, T1]]) is Observable) = observe
      hexagon[T1, T2, T4]
    }
  }
}

/** The laws of [[Cartesian]]: the universal property of products. */
abstract class CartesianSpec(tracked val M: Cartesian { val K: Category { type Obj = Type } })(using
  F: CategoryFixture.On[M.K.type],
  monoidal: TypeName[M.type],
  category: TypeName[M.K.type],
  types: SampleTypes,
  tensor: [X, Y] => (Sample[X], Sample[Y]) ?=> Sample[M.Tensor[X, Y]],
  unit: Sample[M.I],
) extends LawSuite("Cartesian", s"${monoidal.name} on ${category.name}") {
  import types.{T1, T2, T3, T4, given}
  import F.*
  import M.K.-->
  import M.CartesianLaws.*

  private given TensorSample: [X: Sample, Y: Sample] => Sample[M.Tensor[X, Y]] = tensor[X, Y]

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
    val observations = observe[T1, M.Tensor[T2, T3]]
    val hs           = arrow[T1, M.Tensor[T2, T3]]

    forAll(observations, hs) { (observe, h) =>
      given ((T1 --> M.Tensor[T2, T3]) is Observable) = observe
      pairUniqueness(h)
    }
  }

  law("discardUniqueness") {
    val observations = observe[T1, M.I]
    val fs           = arrow[T1, M.I]

    forAll(observations, fs) { (observe, f) =>
      given ((T1 --> M.I) is Observable) = observe
      discardUniqueness(f)
    }
  }

  law("tensorIsProduct") {
    val observations = observe[M.Tensor[T1, T2], M.Tensor[T4, T3]]
    val fs           = arrow[T1, T4]
    val gs           = arrow[T2, T3]

    forAll(observations, fs, gs) { (observe, f, g) =>
      given ((M.Tensor[T1, T2] --> M.Tensor[T4, T3]) is Observable) = observe
      tensorIsProduct(f, g)
    }
  }

  law("pairCongruence") {
    val observations = observe[T1, M.Tensor[T2, T3]]
    val fs           = arrow[T1, T2]
    val gs           = arrow[T1, T3]

    forAll(observations, fs, gs) { (observe, f, g) =>
      given ((T1 --> M.Tensor[T2, T3]) is Observable) = observe
      pairCongruence(f, variant(f), g, variant(g))
    }
  }
}

/** The laws of [[Cocartesian]]: the universal property of coproducts. */
abstract class CocartesianSpec(tracked val M: Cocartesian { val K: Category { type Obj = Type } })(using
  F: CategoryFixture.On[M.K.type],
  monoidal: TypeName[M.type],
  category: TypeName[M.K.type],
  types: SampleTypes,
  tensor: [X, Y] => (Sample[X], Sample[Y]) ?=> Sample[M.Tensor[X, Y]],
  unit: Sample[M.I],
) extends LawSuite("Cocartesian", s"${monoidal.name} on ${category.name}") {
  import types.{T1, T2, T3, T4, given}
  import F.*
  import M.K.-->
  import M.CocartesianLaws.*

  private given TensorSample: [X: Sample, Y: Sample] => Sample[M.Tensor[X, Y]] = tensor[X, Y]

  law("copairInl") {
    val observations = observe[T1, T4]
    val fs           = arrow[T1, T4]
    val gs           = arrow[T2, T4]

    forAll(observations, fs, gs) { (observe, f, g) =>
      given ((T1 --> T4) is Observable) = observe
      copairInl(f, g)
    }
  }

  law("copairInr") {
    val observations = observe[T2, T4]
    val fs           = arrow[T1, T4]
    val gs           = arrow[T2, T4]

    forAll(observations, fs, gs) { (observe, f, g) =>
      given ((T2 --> T4) is Observable) = observe
      copairInr(f, g)
    }
  }

  law("copairUniqueness") {
    val observations = observe[M.Tensor[T1, T2], T4]
    val hs           = arrow[M.Tensor[T1, T2], T4]

    forAll(observations, hs) { (observe, h) =>
      given ((M.Tensor[T1, T2] --> T4) is Observable) = observe
      copairUniqueness(h)
    }
  }

  law("absurdUniqueness") {
    val observations = observe[M.I, T1]
    val fs           = arrow[M.I, T1]

    forAll(observations, fs) { (observe, f) =>
      given ((M.I --> T1) is Observable) = observe
      absurdUniqueness(f)
    }
  }

  law("tensorIsCoproduct") {
    val observations = observe[M.Tensor[T1, T2], M.Tensor[T4, T3]]
    val fs           = arrow[T1, T4]
    val gs           = arrow[T2, T3]

    forAll(observations, fs, gs) { (observe, f, g) =>
      given ((M.Tensor[T1, T2] --> M.Tensor[T4, T3]) is Observable) = observe
      tensorIsCoproduct(f, g)
    }
  }

  law("copairCongruence") {
    val observations = observe[M.Tensor[T1, T2], T4]
    val fs           = arrow[T1, T4]
    val gs           = arrow[T2, T4]

    forAll(observations, fs, gs) { (observe, f, g) =>
      given ((M.Tensor[T1, T2] --> T4) is Observable) = observe
      copairCongruence(f, variant(f), g, variant(g))
    }
  }
}

class TotalProductIsSymmetricTest       extends SymmetricSpec(Total.Product)
class TotalProductIsCartesianTest       extends CartesianSpec(Total.Product)
class ScalaCoproductIsSymmetricTest     extends SymmetricSpec(Total.Coproduct)
class ScalaCoproductIsCocartesianTest   extends CocartesianSpec(Total.Coproduct)
class PartialProductIsSymmetricTest     extends SymmetricSpec(Partial.Product)
class PartialCoproductIsSymmetricTest   extends SymmetricSpec(Partial.Coproduct)
class PartialCoproductIsCocartesianTest extends CocartesianSpec(Partial.Coproduct)
