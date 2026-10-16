package parrot
package category

import scala.util.{Failure, Success, Try}

class StateTTest extends CategorySuite {

  given NamedTuple2CanEqual: [A, B] => CanEqual[(result: A, state: B), (result: A, state: B)] =
    CanEqual.derived

  private val OptionFunctor     = StateT.StateTIsFunctor[Int, Option](using Functor.OptionIsFunctor)
  private val OptionMonad       = StateT.StateTIsMonad[Int, Option](using Monad.OptionIsMonad)
  private val TryMonad          = StateT.StateTIsMonad[Int, Try](using Monad.TryIsMonad)
  private val OptionRestriction =
    StateT.StateTIsRestrictionMonad[Int, Option](using RestrictionMonad.OptionIsRestrictionMonad)
  private val TryRestriction = StateT.StateTIsRestrictionMonad[Int, Try](using RestrictionMonad.TryIsRestrictionMonad)
  private val OptionElgot    = StateT.StateTIsElgotMonad[Int, Option](using ElgotMonad.OptionIsElgotMonad)
  private val TryElgot       = StateT.StateTIsElgotMonad[Int, Try](using ElgotMonad.TryIsElgotMonad)
  private val TryValued      =
    StateT.StateTIsValued[Int, Try, Monoid.Additive](using Valued.TryIsAdditiveValued, Pointwise.AdditiveIsPointwise)

  private val mOption: StateT[Int, Option][Int] =
    s => if s < 0 then None else Some((result = s * 2, state = s + 1))

  private val fOption: Int => StateT[Int, Option][String] =
    a => s => if a % 2 == 0 then Some((result = s"even:$a", state = s + a)) else None

  private val gOption: String => StateT[Int, Option][Boolean] =
    str =>
      s =>
        if str.startsWith("even") then Some((result = true, state = s + str.length))
        else Some((result = false, state = s))

  private val mTry: StateT[Int, Try][Int] =
    s =>
      if s < 0 then Failure(new IllegalArgumentException("negative state"))
      else Success((result = s * 2, state = s + 1))

  private val fTry: Int => StateT[Int, Try][String] =
    a => s => if a % 2 == 0 then Success((result = s"even:$a", state = s + a)) else Failure(new Exception("odd result"))

  private val gTry: String => StateT[Int, Try][Boolean] =
    str =>
      s =>
        if str.startsWith("even") then Success((result = true, state = s + str.length))
        else Success((result = false, state = s))

  test("StateT[Int, Option] is Functor: identity and composition laws") {
    val _                = assert(OptionFunctor.FunctorLaws.identity(mOption))
    val f: Int => String = _.toString
    val g: String => Int = _.length
    assert(OptionFunctor.FunctorLaws.composition(mOption, f, g))
  }

  test("StateT[Int, Option] is Functor: map transforms result and preserves state transitions") {
    val transformed = OptionFunctor.map(mOption)(_ + 10)
    val _           = assert(transformed(2) == Some((result = 14, state = 3)))
    assert(transformed(-1) == None)
  }

  test("StateT[Int, Option] is Monad: monad laws") {
    forAll { (a: Int) =>
      val _ = assert(OptionMonad.MonadLaws.leftIdentity(a, fOption))
      val _ = assert(OptionMonad.MonadLaws.rightIdentity(mOption))
      assert(OptionMonad.MonadLaws.associativity(mOption, fOption, gOption))
    }
  }

  test("StateT[Int, Option] is Monad: unit and multiplication laws") {
    val h: Int => String                                        = _.toString
    val mmOption: StateT[Int, Option][StateT[Int, Option][Int]] =
      OptionMonad.unit(mOption)
    val mmmOption: StateT[Int, Option][StateT[Int, Option][StateT[Int, Option][Int]]] =
      OptionMonad.unit(mmOption)

    val _ = assert(OptionMonad.MonadLaws.unitNaturality(42, h))
    val _ = assert(OptionMonad.MonadLaws.leftUnitality(mOption))
    val _ = assert(OptionMonad.MonadLaws.rightUnitality(mOption))
    val _ = assert(OptionMonad.MonadLaws.multiplicationNaturality(mmOption, h))
    assert(OptionMonad.MonadLaws.multiplicationAssociativity(mmmOption))
  }

  test("StateT[Int, Option] is Monad: unit and flatMap state propagation") {
    val init = OptionMonad.unit(10)
    val _    = assert(init(5) == Some((result = 10, state = 5)))

    val step1: StateT[Int, Option][Int]           = s => Some((result = s, state = s + 1))
    val step2: Int => StateT[Int, Option][String] = prev => s => Some((result = s"prev:$prev,curr:$s", state = s * 2))

    val chained = OptionMonad.flatMap(step1)(step2)
    assert(chained(3) == Some((result = "prev:3,curr:4", state = 8)))
  }

  test("StateT[Int, Try] is Monad: monad laws") {
    forAll { (a: Int) =>
      val _ = assert(TryMonad.MonadLaws.leftIdentity(a, fTry))
      val _ = assert(TryMonad.MonadLaws.rightIdentity(mTry))
      assert(TryMonad.MonadLaws.associativity(mTry, fTry, gTry))
    }
  }

  test("StateT[Int, Try] is Monad: error propagation") {
    val failStep: StateT[Int, Try][Int] = _ => Failure(new RuntimeException("failed"))
    val chained                         = TryMonad.flatMap(failStep)(fTry)
    assert(chained(0).isFailure)
  }

  test("StateT[Int, Option] is RestrictionMonad: restriction laws") {
    val nOption: StateT[Int, Option][String] = s => if s % 2 == 0 then Some((result = "ok", state = s)) else None
    val _                                    = assert(OptionRestriction.RestrictionLaws.absorption(mOption))
    val _                                    = assert(OptionRestriction.RestrictionLaws.commutativity(mOption, nOption))
    val _                                    = assert(OptionRestriction.RestrictionLaws.unitality(42))
    assert(OptionRestriction.RestrictionLaws.idempotence(mOption))
  }

  test("StateT[Int, Option] is RestrictionMonad: restrict resets result to Unit and restores input state") {
    val restricted = OptionRestriction.restrict(mOption)
    val _          = assert(restricted(2) == Some((result = (), state = 2)))
    assert(restricted(-1) == None)
  }

  test("StateT[Int, Try] is RestrictionMonad: restriction laws") {
    val nTry: StateT[Int, Try][String] =
      s => if s % 2 == 0 then Success((result = "ok", state = s)) else Failure(new Exception("odd"))
    val _ = assert(TryRestriction.RestrictionLaws.absorption(mTry))
    val _ = assert(TryRestriction.RestrictionLaws.commutativity(mTry, nTry))
    val _ = assert(TryRestriction.RestrictionLaws.unitality(42))
    assert(TryRestriction.RestrictionLaws.idempotence(mTry))
  }

  test("StateT[Int, Option] is ElgotMonad: iteration computes stateful loop") {
    val countdown: Int => StateT[Int, Option][Either[String, Int]] = n =>
      s => {
        if s < 0 then None
        else if n <= 0 then Some((result = Left(s"done at state $s"), state = s))
        else Some((result = Right(n - 1), state = s + 10))
      }

    val loop = OptionElgot.iterate(countdown)
    val _    = assert(loop(3)(0) == Some((result = "done at state 30", state = 30)))
    val _    = assert(loop(3)(-1) == None)
    forAll((n: Int) => assert(OptionElgot.ElgotLaws.fixedPoint(countdown, n % 10)))
  }

  test("StateT[Int, Try] is ElgotMonad: iteration computes stateful loop and handles failure") {
    val err                                                     = new IllegalArgumentException("state exhausted")
    val countdown: Int => StateT[Int, Try][Either[String, Int]] = n =>
      s => {
        if s >= 100 then Failure(err)
        else if n <= 0 then Success((result = Left(s"done at state $s"), state = s))
        else Success((result = Right(n - 1), state = s + 20))
      }

    val loop = TryElgot.iterate(countdown)
    val _    = assert(loop(3)(0) === Success((result = "done at state 60", state = 60)))
    val _    = assert(loop(10)(0) === Failure(err))
    forAll((n: Int) => assert(TryElgot.ElgotLaws.fixedPoint(countdown, n % 5)))
  }

  test("StateT[Int, Try] is Valued over Monoid.Additive: zero fails and plus falls back") {
    val additive = TryValued.FIsV[String]
    val zero     = additive.zero
    val _        = assert(zero(0).isFailure)

    val failStep: StateT[Int, Try][String] = _ => Failure(new Exception("first failed"))
    val okStep: StateT[Int, Try][String]   = s => Success((result = "fallback", state = s + 1))

    val combined = additive.plus(failStep, okStep)
    assert(combined(10) === Success((result = "fallback", state = 11)))
  }
}
