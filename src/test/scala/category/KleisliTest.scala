package parrot
package category

class KleisliTest extends CategorySuite {
  private val Profunctor  = Kleisli.KleisliIsProfunctor[Option]
  private val Promonad    = Kleisli.KleisliIsPromonad[Option]
  private val Strong      = Kleisli.KleisliIsStrong[Option]
  private val Cocartesian = Kleisli.KleisliIsCocartesian[Option]
  private val Restriction = Kleisli.KleisliIsRestriction[Option]
  private val Elgot       = Kleisli.KleisliIsElgot[Option]

  private val p: Int => Option[String]     = i => if i % 3 == 0 then None else Some(s"v$i")
  private val q: String => Option[Boolean] = s => if s.length > 3 then Some(s.length % 2 == 0) else None
  private val r: Boolean => Option[Int]    = b => if b then Some(1) else None
  private val s: Int => Option[Boolean]    = i => if i > 0 then Some(i % 2 == 0) else None

  test("Kleisli[Option] is Profunctor: identity and composition") {
    val _                     = assert(Profunctor.ProfunctorLaws.identity(p))
    val f1: Boolean => Int    = if _ then 1 else 0
    val g1: String => Int     = _.length
    val f2: Double => Boolean = _ > 0.0
    val g2: Int => String     = _.toString
    assert(Profunctor.ProfunctorLaws.composition(p, f1, g1, f2, g2))
  }

  test("Kleisli[Option] is Promonad: identity and associativity") {
    val _ = assert(Promonad.PromonadLaws.leftIdentity(p))
    val _ = assert(Promonad.PromonadLaws.rightIdentity(p))
    assert(Promonad.PromonadLaws.associativity(p, q, r))
  }

  test("Kleisli[Option] is Strong: unitality and associativity") {
    val _ = assert(Strong.StrongLaws.firstUnitality(p))
    val _ = assert(Strong.StrongLaws.secondUnitality(p))
    val _ = assert(Strong.StrongLaws.firstAssociativity[Int, String, Boolean, Int](p))
    assert(Strong.StrongLaws.secondAssociativity[Int, String, Boolean, Int](p))
  }

  test("Kleisli[Option] is Cocartesian: injections and copairing") {
    val _ = assert(Cocartesian.CocartesianLaws.leftInjection(p, (b: Boolean) => Some(b.toString)))
    val _ = assert(Cocartesian.CocartesianLaws.rightInjection(p, (b: Boolean) => Some(b.toString)))
    assert(Cocartesian.CocartesianLaws.sumUniqueness[Int, String])
  }

  test("Kleisli[Option] is Restriction: restriction laws") {
    val _ = assert(Restriction.RestrictionLaws.restrictionIdentity(p))
    val _ = assert(Restriction.RestrictionLaws.restrictionCommutativity(p, s))
    val _ = assert(Restriction.RestrictionLaws.restrictionCompose(p, s))
    assert(Restriction.RestrictionLaws.restrictionPrecompose(p, q))
  }

  test("Kleisli[Option] is Elgot: fixed point law") {
    val step: Int => Option[Either[String, Int]] = i => {
      if i < -50 then None else if i <= 0 || i >= 50 then Some(Left(s"done:$i")) else Some(Right(i - 7))
    }
    val _ = assert(Elgot.dagger(step)(20) == Some("done:-1"))
    assert(Elgot.ElgotLaws.fixedPoint[String, Int](step))
  }

  test("Kleisli[Option] is Enriched over Fixed: recursion in hom-sets") {
    val fixOp   = Fixed.FunctionIsFixed[Int, Option[Int]]
    val collatz = fixOp.fix { self => n =>
      if n <= 1 then Some(0)
      else if n > 1000 then None
      else self(if n % 2 == 0 then n / 2 else 3 * n + 1).map(_ + 1)
    }
    val _ = assert(collatz(6) == Some(8))
    assert(collatz(27) == None)
  }
}
