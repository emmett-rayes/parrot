package parrot
package category

class FunctorTest extends CategorySuite {

  private val OptionFunctor = Functor.OptionIsFunctor

  test("Option is Functor: functor laws") {
    forAll { (m: Option[Int]) =>
      val _ = assert(OptionFunctor.FunctorLaws.identity(m))
      val f: Int => String = _.toString
      val g: String => Int = _.length
      assert(OptionFunctor.FunctorLaws.composition(m, f, g))
    }
  }

  test("Option is Functor: map behaves as Option.map") {
    val _ = assert(OptionFunctor.map(Some(42))(_ + 1) == Some(43))
    assert(OptionFunctor.map(None: Option[Int])(_ + 1) == None)
  }

  test("Option is Functor: extension behaves as Option.map") {
    import OptionFunctor.map
    val _ = assert(Some(42).map(_ + 1) == Some(43))
    assert((None: Option[Int]).map(_ + 1) == None)
  }
}
