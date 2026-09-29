package parrot
package category

class SymmetricTest extends CategorySuite {

  // =========================================================================
  // Symmetric Laws on Function
  // =========================================================================

  private val FunctionLaws = Symmetric.FunctionIsSymmetric.SymmetricLaws

  test("Function is Symmetric: braid naturality law") {
    val f1: Int => String     = i => if i >= 0 then s"pos:$i" else s"neg:$i"
    val g1: Boolean => Double = if _ then 1.0 else 0.0
    val _                     = assert(FunctionLaws.braidNaturality(f1, g1))

    val f2: String => Int    = _.length
    val g2: Double => String = d => s"val:$d"
    val _                    = assert(FunctionLaws.braidNaturality(f2, g2))

    val f3: Int => Int        = _ * 2
    val g3: String => Boolean = _.nonEmpty
    assert(FunctionLaws.braidNaturality(f3, g3))
  }

  test("Function is Symmetric: symmetry law") {
    val _ = assert(FunctionLaws.symmetry[Int, String])
    val _ = assert(FunctionLaws.symmetry[Double, Boolean])
    assert(FunctionLaws.symmetry[(Int, String), Boolean])
  }

  test("Function is Symmetric: hexagon law") {
    val _ = assert(FunctionLaws.hexagon[Int, String, Boolean])
    val _ = assert(FunctionLaws.hexagon[Double, Int, String])
    assert(FunctionLaws.hexagon[String, Boolean, (Int, Int)])
  }

  test("Function is Symmetric: right unitor consistency law") {
    val _ = assert(FunctionLaws.rightUnitorConsistency[Int])
    val _ = assert(FunctionLaws.rightUnitorConsistency[String])
    assert(FunctionLaws.rightUnitorConsistency[Boolean])
  }

  test("Function is Symmetric: unassociate 5-braid composite isomorphism") {
    val F = Symmetric.FunctionIsSymmetric
    val P = Promonad[Function]
    import P.>>>

    val iso1 = (F.associate[Int, String, Boolean] >>> F.unassociate[Int, String, Boolean]) ===
      P.identity[((Int, String), Boolean)]
    val iso2 = (F.unassociate[Int, String, Boolean] >>> F.associate[Int, String, Boolean]) ===
      P.identity[(Int, (String, Boolean))]
    val _ = assert(iso1)
    assert(iso2)
  }
}
