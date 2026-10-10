package parrot
package category

class KleisliTest extends CategorySuite {
  import Kleisli.given

  private val Promonad    = Kleisli.KleisliIsPromonad[Option]
  private val Strong      = Kleisli.KleisliIsStrong[Option]
  private val Cocartesian = Kleisli.KleisliIsCocartesian[Option]
  private val Restriction = Kleisli.KleisliIsRestriction[Option]
  private val Elgot       = Kleisli.KleisliIsElgot[Option]
  private val Enriched    = Kleisli.KleisliIsEnriched[Option]

  private val p: Int => Option[String]     = i => if i % 3 == 0 then None else Some(s"v$i")
  private val q: String => Option[Boolean] = s => if s.length > 3 then Some(s.length % 2 == 0) else None
  private val r: Boolean => Option[Int]    = b => if b then Some(1) else None
  private val s: Int => Option[Boolean]    = i => if i > 0 then Some(i % 2 == 0) else None

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

  test("Kleisli[Option] is Enriched over additive monoids: pointwise ordered choice") {
    val plus = Enriched.HomIsV[Int, String]
    val alt  = plus.plus(p, i => Some(s"alt$i"))
    val _    = assert(alt(3) == Some("alt3"))
    val _    = assert(alt(4) == Some("v4"))
    assert(plus.plus(plus.zero, p)(4) == p(4))
  }
}
