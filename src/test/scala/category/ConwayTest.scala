package parrot
package category

class ConwayTest extends CategorySuite {

  private val ConwayInstance = Conway.FunctionIsLazyCartesianConway
  private val ConwayLaws     = ConwayInstance.ConwayLaws

  // =========================================================================
  // Basic Conway Dagger on Function
  // =========================================================================

  test("Function is Conway: dagger evaluation computes fixed point") {
    // p(a, c) = a + c/2 => fixed point c = 2a
    // Using knot-tying lazy tuple: p(a, c) = a + 10 => c = a + 10
    val p: LazyTuple2[Int, Int] => Int = p => p._1 + 10
    val daggered                       = ConwayInstance.dagger(p)
    assert(daggered(5) == 15)
  }

  test("Function is Conway: knot-tying recursive stream generation") {
    // Generate an infinite stream / list up to n elements
    val p: LazyTuple2[Int, LazyList[Int]] => LazyList[Int] = p => {
      if p._1 <= 0 then LazyList.empty
      else p._1 #:: p._2.take(p._1 - 1)
    }
    val gen = ConwayInstance.dagger(p)
    assert(gen(4).toList == List(4, 4, 4, 4))
  }

  // =========================================================================
  // Conway Laws on Function
  // =========================================================================

  test("Function is Conway satisfies fixedPoint law") {
    val p: LazyTuple2[Int, Int => String] => (Int => String) =
      p => x => s"${p._1 * 2 + x}"
    assert(ConwayLaws.fixedPoint[Int, Int => String](p))
  }

  test("Function is Conway satisfies parameterNaturality law") {
    val p: LazyTuple2[Int, Int => String] => (Int => String) =
      p => x => s"${p._1 + x}"
    val h: String => Int = _.length
    assert(ConwayLaws.parameterNaturality[String, Int, Int => String](p, h))
  }

  test("Function is Conway satisfies composition law") {
    val p: LazyTuple2[Int, Int] => Int =
      pair => pair._1 * 2 + 3
    val g: Int => Int = x => x + 5
    assert(ConwayLaws.composition[Int, Int, Int](p, g))
  }

  test("Function is Conway satisfies doubleDagger law") {
    val p: LazyTuple2[LazyTuple2[Int, Int => String], Int => String] => (Int => String) =
      p => x => s"${p._1._1 + x}"
    assert(ConwayLaws.doubleDagger[Int, Int => String](p))
  }

  // =========================================================================
  // Convertible: Conway -> Traced (with Cartesian)
  // =========================================================================

  test("ConwayIsCartesianTraced: derived left and right trace work correctly") {
    val traced = Conway.ConwayIsCartesianTraced

    // left trace on Function
    // p: (A * C) -> (B * C), where * is LazyTuple2
    val p: LazyTuple2[Int, Int] => LazyTuple2[Int, Int] = p => LazyTuple2(p._1 + p._2, 10)
    val res: Int => Int                                 = traced.left(p)

    // right trace on Function
    // q: (C * A) -> (C * B)
    val q: LazyTuple2[Int, Int] => LazyTuple2[Int, Int] = p => LazyTuple2(20, p._2 * 2 + p._1)
    val resRight: Int => Int                            = traced.right(q)
    assert(res(5) == 15 && resRight(3) == 26)
  }

  test("ConwayIsCartesianTraced satisfies TracedLaws") {
    val traced = Conway.ConwayIsCartesianTraced
    val laws   = traced.TracedLaws

    val p: LazyTuple2[Int, Boolean] => LazyTuple2[String, Boolean] = p => LazyTuple2(s"${p._1}-${p._2}", false)
    val f: Double => Int                                           = _.toInt
    val g: String => Int                                           = _.length
    assert(laws.leftNaturality[Int, String, Double, Int, Boolean](p, f, g))
  }

  // =========================================================================
  // Convertible: Cartesian + Traced -> Conway
  // =========================================================================

  test("CartesianTracedIsConway: derived dagger works correctly") {
    val prom   = summon[Function is Promonad]
    val cart   = Cartesian.FunctionIsLazyCartesian
    val traced = Traced.FunctionIsLazyCartesianTraced

    val conway = Conway.CartesianTracedIsConway(using prom, cart, traced)

    val p: LazyTuple2[Int, Int] => Int = p => p._1 + 10
    val fixed: Int => Int              = conway.dagger(p)
    assert(fixed(5) == 15)
  }

  test("CartesianTracedIsConway satisfies ConwayLaws") {
    val prom   = summon[Function is Promonad]
    val cart   = Cartesian.FunctionIsLazyCartesian
    val traced = Traced.FunctionIsLazyCartesianTraced

    val conway = Conway.CartesianTracedIsConway(using prom, cart, traced)
    val laws   = conway.ConwayLaws

    val p: LazyTuple2[Int, Int => String] => (Int => String) =
      p => x => s"${p._1 * 3 + x}"
    assert(laws.fixedPoint[Int, Int => String](p)(using cart))
  }

  test("Roundtrip conversion: Conway -> Traced -> Conway preserves dagger") {
    val tracedDerived   = Conway.ConwayIsCartesianTraced
    val prom            = summon[Function is Promonad]
    val conwayRoundtrip = Conway.CartesianTracedIsConway(using prom, ConwayInstance.OnIsCartesian, tracedDerived)

    val p: LazyTuple2[Int, Int] => Int = p => p._1 * 7 + 3
    val daggerRoundtrip: Int => Int    = conwayRoundtrip.dagger(p)
    assert(daggerRoundtrip(4) == ConwayInstance.dagger(p)(4))
  }
}
