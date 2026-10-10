package parrot
package category

class FixedTest extends CategorySuite {

  private val FunctionFixed = Fixed.FunctionIsFixed[Int, Int]
  private val FunctionLaws  = FunctionFixed.FixedLaws

  test("Function is Fixed: fix ties the knot by eta-expansion") {
    val factorial = FunctionFixed.fix(self => n => if n <= 1 then 1 else n * self(n - 1))
    assert(factorial(5) == 120)
  }

  test("Function is Fixed satisfies fixedPoint law") {
    val f: (Int => Int) => (Int => Int) = self => n => if n <= 0 || n > 1000 then 0 else 1 + self(n / 2)
    assert(FunctionLaws.fixedPoint(f))
  }

  test("Function is Fixed satisfies dinaturality law") {
    val f: (Int => Int) => (Int => String) = h => n => if n <= 0 || n > 1000 then "." else h(n / 2).toString
    val g: (Int => String) => (Int => Int) = k => n => if n <= 0 || n > 1000 then 0 else k(n / 2).length + 1
    assert(FunctionLaws.dinaturality(f, g))
  }

  test("Function is Fixed satisfies diagonal law") {
    val f: (Int => Int, Int => Int) => (Int => Int) = {
      (x, y) => n => if n <= 0 || n > 1000 then 0 else x(n / 2) + y(n / 3) + 1
    }
    assert(FunctionLaws.diagonal(f))
  }

  test("Tuple2 is Fixed: mutual recursion via Bekić's theorem") {
    val fixed       = summon[(Int => Boolean, Int => Boolean) is Fixed]
    val (even, odd) = fixed.fix((even, odd) => (n => n == 0 || odd(n - 1), n => n != 0 && even(n - 1)))
    val _           = assert(even(10) && !even(7))
    assert(odd(7) && !odd(10))
  }

  // =========================================================================
  // Relation to Conway and Closed
  // =========================================================================

  test("Function is Fixed agrees with the Conway dagger: p† = Λ(p) ⨾ fix") {
    val conway = Conway.FunctionIsLazyCartesianConway
    val closed = Closed.FunctionIsLazyClosed
    val fixed  = Fixed.FunctionIsFixed[Int, Int]

    val p: LazyTuple2[Int, Int => Int] => (Int => Int) = t => n => if n <= 0 then t._1 else n + t._2(n - 1)
    val viaFixed: Int => (Int => Int)                  = closed.curry(p).andThen(fixed.fix)
    val viaDagger: Int => (Int => Int)                 = conway.dagger(p)
    assert((0 to 5).forall(a => (0 to 5).forall(n => viaFixed(a)(n) == viaDagger(a)(n))))
  }

  test("Fixed.exponential computes fixed points on exponentials") {
    val fix = Fixed.exponential[Function, Unit, LazyTuple2, Function, Int, Int](
      using Conway.FunctionIsLazyCartesianConway,
      Closed.FunctionIsLazyClosed,
    )
    val fib = fix(self => n => if n <= 1 then n else self(n - 1) + self(n - 2))
    assert(fib(10) == 55)
  }
}
