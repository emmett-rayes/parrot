package parrot
package category

class TracedTest extends CategorySuite {

  // =========================================================================
  // Cartesian Traced Laws on Function (Lazy knot-tying / fixed points)
  // =========================================================================

  private val CartesianLaws = Traced.FunctionIsLazyCartesianTraced.TracedLaws

  test("Function is Cartesian Traced: left evaluation") {
    // p(a, c) = (a + c, 10) => fixed point c = 10, returns a + 10
    val p: LazyTuple2[Int, Int] => LazyTuple2[Int, Int] = p => LazyTuple2(p._1 + p._2, 10)
    val traced                                          = Traced.FunctionIsLazyCartesianTraced.left(p)
    assert(traced(5) == 15)
  }

  test("Function is Cartesian Traced: right evaluation") {
    // p(c, a) = (10, a + c) => fixed point c = 10, returns a + 10
    val p: LazyTuple2[Int, Int] => LazyTuple2[Int, Int] = p => LazyTuple2(10, p._2 + p._1)
    val traced                                          = Traced.FunctionIsLazyCartesianTraced.right(p)
    assert(traced(5) == 15)
  }

  test("Function is Cartesian Traced: left naturality law") {
    val p: LazyTuple2[Int, Boolean] => LazyTuple2[String, Boolean] = p => LazyTuple2(s"${p._1}:${p._2}", true)
    val f: Double => Int                                           = _.toInt
    val g: String => Int                                           = _.length
    assert(CartesianLaws.leftNaturality[Int, String, Double, Int, Boolean](p, f, g))
  }

  test("Function is Cartesian Traced: right naturality law") {
    val p: LazyTuple2[Boolean, Int] => LazyTuple2[Boolean, String] = p => LazyTuple2(true, s"${p._2}:${p._1}")
    val f: Double => Int                                           = _.toInt
    val g: String => Int                                           = _.length
    assert(CartesianLaws.rightNaturality[Int, String, Double, Int, Boolean](p, f, g))
  }

  test("Function is Cartesian Traced: left unitality law") {
    val p: Int => String = i => s"val:$i"
    assert(CartesianLaws.leftUnitality(p))
  }

  test("Function is Cartesian Traced: right unitality law") {
    val p: Int => String = i => s"val:$i"
    assert(CartesianLaws.rightUnitality(p))
  }

  test("Function is Cartesian Traced: left associativity law") {
    val p: LazyTuple2[LazyTuple2[Int, Boolean], Double] => LazyTuple2[LazyTuple2[String, Boolean], Double] = {
      p => LazyTuple2(LazyTuple2(s"${p._1._1}:${p._1._2}:${p._2}", true), 1.0)
    }
    assert(CartesianLaws.leftAssociativity[Int, String, Boolean, Double](p))
  }

  test("Function is Cartesian Traced: right associativity law") {
    val p: LazyTuple2[Double, LazyTuple2[Boolean, Int]] => LazyTuple2[Double, LazyTuple2[Boolean, String]] = {
      p => LazyTuple2(1.0, LazyTuple2(true, s"${p._2._2}:${p._2._1}:${p._1}"))
    }
    assert(CartesianLaws.rightAssociativity[Int, String, Boolean, Double](p))
  }

  test("Function is Cartesian Traced: extension methods") {
    val C = Traced.FunctionIsLazyCartesianTraced
    import C.*

    val pLeft: LazyTuple2[Int, Int] => LazyTuple2[Int, Int] = p => LazyTuple2(p._1 + p._2, 10)
    val _                                                   = assert(pLeft.left(5) == 15)

    val pRight: LazyTuple2[Int, Int] => LazyTuple2[Int, Int] = p => LazyTuple2(10, p._2 + p._1)
    assert(pRight.right(5) == 15)
  }

  // =========================================================================
  // Cocartesian Traced Laws on Function (Iteration / tail-recursion)
  // =========================================================================

  private val CocartesianLaws = Traced.FunctionIsCocartesianTraced.TracedLaws

  test("Function is Cocartesian Traced: left while loop execution") {
    // Computes sum 1..n via state loop
    // Either[Int, (Int, Int)] => Either[Int, (Int, Int)]
    val step: Either[Int, (Int, Int)] => Either[Int, (Int, Int)] = {
      case Left(n)         => Right((0, n))
      case Right((acc, n)) =>
        if n <= 0 then Left(acc)
        else Right((acc + n, n - 1))
    }
    val sumToN = Traced.FunctionIsCocartesianTraced.left(step)
    assert(sumToN(10) == 55)
  }

  test("Function is Cocartesian Traced: right while loop execution") {
    // Computes sum 1..n via state loop
    // Either[(Int, Int), Int] => Either[(Int, Int), Int]
    val step: Either[(Int, Int), Int] => Either[(Int, Int), Int] = {
      case Right(n)       => Left((0, n))
      case Left((acc, n)) =>
        if n <= 0 then Right(acc)
        else Left((acc + n, n - 1))
    }
    val sumToN = Traced.FunctionIsCocartesianTraced.right(step)
    assert(sumToN(10) == 55)
  }

  test("Function is Cocartesian Traced: left naturality law") {
    val p: Either[Int, String] => Either[Double, String] = {
      case Left(i)  => Left(i.toDouble * 2.0)
      case Right(s) => Left(s.length.toDouble)
    }
    val f: Boolean => Int   = if _ then 1 else 0
    val g: Double => String = d => s"res:$d"
    assert(CocartesianLaws.leftNaturality[Int, Double, Boolean, String, String](p, f, g))
  }

  test("Function is Cocartesian Traced: right naturality law") {
    val p: Either[String, Int] => Either[String, Double] = {
      case Right(i) => Right(i.toDouble * 2.0)
      case Left(s)  => Right(s.length.toDouble)
    }
    val f: Boolean => Int   = if _ then 1 else 0
    val g: Double => String = d => s"res:$d"
    assert(CocartesianLaws.rightNaturality[Int, Double, Boolean, String, String](p, f, g))
  }

  test("Function is Cocartesian Traced: left unitality law") {
    val p: Int => String = i => s"val:$i"
    assert(CocartesianLaws.leftUnitality(p))
  }

  test("Function is Cocartesian Traced: right unitality law") {
    val p: Int => String = i => s"val:$i"
    assert(CocartesianLaws.rightUnitality(p))
  }

  test("Function is Cocartesian Traced: left associativity law") {
    val p: Either[Either[Int, Boolean], Double] => Either[Either[String, Boolean], Double] = {
      case Left(Left(i))  => Left(Left(s"val:$i"))
      case Left(Right(b)) => Left(Left(s"bool:$b"))
      case Right(d)       => Left(Left(s"double:$d"))
    }
    assert(CocartesianLaws.leftAssociativity[Int, String, Boolean, Double](p))
  }

  test("Function is Cocartesian Traced: right associativity law") {
    val p: Either[Double, Either[Boolean, Int]] => Either[Double, Either[Boolean, String]] = {
      case Right(Right(i)) => Right(Right(s"val:$i"))
      case Right(Left(b))  => Right(Right(s"bool:$b"))
      case Left(d)         => Right(Right(s"double:$d"))
    }
    assert(CocartesianLaws.rightAssociativity[Int, String, Boolean, Double](p))
  }
}
