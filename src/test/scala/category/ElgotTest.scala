package parrot
package category

class ElgotTest extends CategorySuite {

  private val ElgotInstance = Elgot.FunctionIsCocartesianElgot
  private val ElgotLaws     = ElgotInstance.ElgotLaws

  // =========================================================================
  // Basic Elgot Dagger on Function
  // =========================================================================

  test("Function is Elgot: dagger evaluation computes tail-recursive loop") {
    // p(c) = if c >= 10 then Left(s"done:$c") else Right(c + 3)
    val p: Int => Either[String, Int] = c => {
      if c >= 10 then Left(s"done:$c")
      else Right(c + 3)
    }
    val loop = ElgotInstance.dagger(p)
    assert(loop(1) == "done:10")
  }

  test("Function is Elgot: accumulator-based factorial loop") {
    // State is (n, acc), exits with final acc
    val p: ((Int, BigInt)) => Either[BigInt, (Int, BigInt)] = { case (n, acc) =>
      if n <= 1 then Left(acc)
      else Right((n - 1, acc * n))
    }
    val fact = ElgotInstance.dagger(p)
    assert(fact((5, BigInt(1))) == BigInt(120))
  }

  // =========================================================================
  // Elgot Laws on Function
  // =========================================================================

  test("Function is Elgot satisfies fixedPoint law") {
    val p: Int => Either[String, Int] = c => {
      if c <= 0 || c >= 5 then Left(s"res:$c")
      else Right(c - 1)
    }
    assert(ElgotLaws.fixedPoint[String, Int](p))
  }

  test("Function is Elgot satisfies parameterNaturality law") {
    val p: Int => Either[Int, Int] = c => {
      if c <= 0 || c >= 5 then Left(c * 2)
      else Right(c - 1)
    }
    val h: Int => String = i => s"val:$i"
    assert(ElgotLaws.parameterNaturality[Int, String, Int](p, h))
  }

  test("Function is Elgot satisfies composition law") {
    val p: Int => Either[String, Int] = d => {
      if d <= 0 || d >= 10 then Left(s"exit:$d")
      else Right(d - 2)
    }
    val g: Int => Int = c => if c <= 0 then 0 else c - 1
    assert(ElgotLaws.composition[String, Int, Int](p, g))
  }

  test("Function is Elgot satisfies doubleDagger law") {
    val p: Int => Either[Either[String, Int], Int] = c => {
      if c <= 0 || c >= 10 then Left(Left(s"done:$c"))
      else if c % 2 == 0 then Left(Right(c - 2))
      else Right(c - 1)
    }
    assert(ElgotLaws.doubleDagger[String, Int](p))
  }

  test("Function is Elgot satisfies uniformity law") {
    val f: Int => Either[String, Int] = c => {
      if c <= 0 || c >= 4 then Left(s"num:${c * 2}")
      else Right(c - 1)
    }
    val g: Int => Either[String, Int] = c => {
      if c <= 0 || c >= 8 then Left(s"num:$c")
      else Right(c - 2)
    }
    val h: Int => Int = c => c * 2
    assert(ElgotLaws.uniformity[String, Int, Int](f, g, h))
  }

  // =========================================================================
  // Convertible: Elgot -> Traced (with Cocartesian)
  // =========================================================================

  test("ElgotIsCocartesianTraced: derived left and right trace work correctly") {
    val traced = Elgot.ElgotIsCocartesianTraced

    // left trace on Function
    // p: Either[Int, (Int, Int)] => Either[Int, (Int, Int)]
    val step: Either[Int, (Int, Int)] => Either[Int, (Int, Int)] = {
      case Left(n)         => Right((0, n))
      case Right((acc, n)) =>
        if n <= 0 then Left(acc)
        else Right((acc + n, n - 1))
    }
    val sumToN = traced.left(step)

    // right trace on Function
    // q: Either[(Int, Int), Int] => Either[(Int, Int), Int]
    val stepRight: Either[(Int, Int), Int] => Either[(Int, Int), Int] = {
      case Right(n)       => Left((0, n))
      case Left((acc, n)) =>
        if n <= 0 then Right(acc)
        else Left((acc + n, n - 1))
    }
    val sumToNRight = traced.right(stepRight)
    assert(sumToN(10) == 55 && sumToNRight(10) == 55)
  }

  test("ElgotIsCocartesianTraced satisfies TracedLaws") {
    val traced = Elgot.ElgotIsCocartesianTraced
    val laws   = traced.TracedLaws

    val p: Either[Int, String] => Either[Double, String] = {
      case Left(i)  => Left(i.toDouble * 2.0)
      case Right(s) => Left(s.length.toDouble)
    }
    val f: Boolean => Int   = if _ then 1 else 0
    val g: Double => String = d => s"res:$d"
    assert(laws.leftNaturality[Int, Double, Boolean, String, String](p, f, g))
  }

  // =========================================================================
  // Convertible: Cocartesian + Traced -> Elgot
  // =========================================================================

  test("CocartesianTracedIsElgot: derived dagger works correctly") {
    val cocart = Cocartesian.FunctionIsCocartesian
    val traced = Traced.FunctionIsCocartesianTraced

    val elgot = Elgot.CocartesianTracedIsElgot(using cocart)(using traced)

    val p: Int => Either[String, Int] = c => {
      if c >= 10 then Left(s"done:$c")
      else Right(c + 3)
    }
    val fixed = elgot.dagger(p)
    assert(fixed(1) == "done:10")
  }

  test("CocartesianTracedIsElgot satisfies ElgotLaws") {
    val cocart = Cocartesian.FunctionIsCocartesian
    val traced = Traced.FunctionIsCocartesianTraced

    val elgot = Elgot.CocartesianTracedIsElgot(using cocart)(using traced)
    val laws  = elgot.ElgotLaws

    val p: Int => Either[String, Int] = c => {
      if c <= 0 || c >= 5 then Left(s"res:$c")
      else Right(c - 1)
    }
    assert(laws.fixedPoint[String, Int](p))
  }

  test("Roundtrip conversion: Elgot -> Traced -> Elgot preserves dagger") {
    val tracedDerived  = Elgot.ElgotIsCocartesianTraced
    val elgotRoundtrip =
      Elgot.CocartesianTracedIsElgot(using ElgotInstance.SelfIsCocartesian)(using tracedDerived)

    val p: Int => Either[String, Int] = c => {
      if c >= 10 then Left(s"val:$c")
      else Right(c + 2)
    }
    val daggerRoundtrip = elgotRoundtrip.dagger(p)
    assert(daggerRoundtrip(2) == ElgotInstance.dagger(p)(2))
  }
}
