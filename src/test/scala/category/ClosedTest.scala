package parrot
package category

class ClosedTest extends CategorySuite {

  // =========================================================================
  // 1. Closed on Function under Tuple2
  // =========================================================================

  private val FunctionInstance = Closed.FunctionIsClosed
  private val FunctionLaws     = FunctionInstance.ClosedLaws

  test("Function is Closed: eval applies and curry transposes") {
    val f: ((Int, String)) => String = (n, s) => s * n
    val _                            = assert(FunctionInstance.eval(((s: String) => s.length, "abc")) == 3)
    assert(FunctionInstance.curry(f)(2)("ab") == "abab")
  }

  test("Function is Closed satisfies beta law") {
    val f: ((Int, String)) => Boolean = (n, s) => s.length == n
    assert(FunctionLaws.beta(f))
  }

  test("Function is Closed satisfies eta law") {
    val g: Int => (String => Boolean) = n => s => s.length > n
    assert(FunctionLaws.eta(g))
  }

  // =========================================================================
  // 2. Closed on Function under LazyTuple2
  // =========================================================================

  private val LazyInstance = Closed.FunctionIsLazyClosed
  private val LazyLaws     = LazyInstance.ClosedLaws

  test("Function is lazily Closed: eval applies and curry transposes") {
    val f: LazyTuple2[Int, String] => String = t => t._2 * t._1
    val length: String => Int                = _.length
    val _                                    = assert(LazyInstance.eval(LazyTuple2(length, "abc")) == 3)
    assert(LazyInstance.curry(f)(2)("ab") == "abab")
  }

  test("Function is lazily Closed satisfies eta law") {
    val g: Int => (String => Boolean) = n => s => s.length > n
    assert(LazyLaws.eta(g))
  }

  test("Function is lazily Closed satisfies beta law on sampled inputs") {
    given ((LazyTuple2[Int, String] => Boolean) is Eq) = new ((LazyTuple2[Int, String] => Boolean) is Eq) {
      def eq(x: LazyTuple2[Int, String] => Boolean, y: LazyTuple2[Int, String] => Boolean): Boolean = {
        List(0, 1, 3).forall(n => List("", "a", "abc").forall(s => x(LazyTuple2(n, s)) == y(LazyTuple2(n, s))))
      }
    }
    val f: LazyTuple2[Int, String] => Boolean = t => t._2.length == t._1
    assert(LazyLaws.beta(f))
  }
}
