package parrot
package legacy

import org.scalacheck.{Arbitrary, Shrink}
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.scalacheck.ScalaCheckPropertyChecks

import scala.annotation.targetName
import scala.util.{Failure, Success, Try}

given arbParserState: Arbitrary[ParserState] =
  Arbitrary(Arbitrary.arbitrary[String].map(s => ParserState.empty(s.asTokens)))
given shrinkParserState: Shrink[ParserState] =
  Shrink(st => Shrink.shrink(st.tokens.toString).map(s => ParserState.empty(s.asTokens)))

class ParserLawsTest extends AnyFunSuite with ScalaCheckPropertyChecks {

  import ElgotMonad.given
  import Functor.given
  import Kleisli.given
  import Monad.given
  import Parser.{run, given}
  import Promonad.given
  import StateT.given

  private val CSP  = CocartesianStrongProfunctor[Parser]
  private val Cat  = Category[Parser]
  private val EP   = ElgotPromonad[Parser]
  private val MP   = CartesianMonoidalProfunctor[Parser]
  private val PA   = ParserAlgebra[Parser]
  private val PMP  = PromonoidPlus[Parser]
  private val ProM = Promonad[Parser]
  private val Prof = Profunctor[Parser]
  private val RP   = RestrictionPromonad[Parser]
  private val SP   = CartesianStrongProfunctor[Parser]

  import CSP.*
  import Cat.*
  import EP.dagger
  import MP.*
  import PMP.*
  import Prof.{dimap, lmap}
  import RP.*
  import SP.*

  // --- Observational Equivalence Helpers ---

  extension [B](t1: Try[(result: B, state: ParserState)])
    @targetName("eqResult")
    infix def ===(t2: Try[(result: B, state: ParserState)]): Boolean = (t1, t2) match {
      case (Success(s1), Success(s2)) => s1.result == s2.result && s1.state.tokens == s2.state.tokens
      case (Failure(e1), Failure(e2)) => e1.getMessage == e2.getMessage
      case _                          => false
    }

  extension [B](t1: Try[(result: B, state: ParserState)])
    // Equivalence up to failure identification
    @targetName("eqResultFailureNorm")
    infix def =~=(t2: Try[(result: B, state: ParserState)]): Boolean = (t1, t2) match {
      case (Success(s1), Success(s2)) => s1.result == s2.result && s1.state.tokens == s2.state.tokens
      case (Failure(_), Failure(_))   => true
      case _                          => false
    }

  // =========================================================================
  // Category Laws on Parser
  // =========================================================================

  test("Category: Parser left identity") {
    val p = PA.literal("abc")
    forAll { (st: ParserState) =>
      val lhs = Cat.id[String].compose(p)
      assert(lhs.run(st) === p.run(st))
    }
  }

  test("Category: Parser right identity") {
    val p = PA.literal("abc")
    forAll { (st: ParserState) =>
      val lhs = p.compose(Cat.id[Unit])
      assert(lhs.run(st) === p.run(st))
    }
  }

  test("Category: Parser associativity") {
    val p1: Parser[Unit, String]   = PA.literal("a")
    val p2: Parser[String, String] = PA.literal("b").lmap((_: String) => ())
    val p3: Parser[String, String] = PA.literal("c").lmap((_: String) => ())
    forAll { (st: ParserState) =>
      val lhs = p3.compose(p2).compose(p1)
      val rhs = p3.compose(p2.compose(p1))
      assert(lhs.run(st) === rhs.run(st))
    }
  }

  // =========================================================================
  // Profunctor Laws on Parser
  // =========================================================================

  test("Profunctor: Parser identity law") {
    val p = PA.literal("hello")
    forAll { (st: ParserState) =>
      val mapped = p.dimap(identity[Unit], identity[String])
      assert(mapped.run(st) === p.run(st))
    }
  }

  test("Profunctor: Parser composition law") {
    val p                  = PA.literal("hello")
    val f1: Int => Unit    = _ => ()
    val f2: Boolean => Int = b => if b then 1 else 0
    val g1: String => Int  = _.length
    val g2: Int => String  = _.toString
    forAll { (b: Boolean, st: ParserState) =>
      val lhs = p.dimap(f1, g1).dimap(f2, g2)
      val rhs = p.dimap(f2.andThen(f1), g1.andThen(g2))
      assert(lhs.run(b, st) === rhs.run(b, st))
    }
  }

  // =========================================================================
  // Promonad Laws on Parser
  // =========================================================================

  test("Promonad: Parser left unitality") {
    val p = PA.literal("xyz")
    forAll { (st: ParserState) =>
      val idUnit = ProM.unit(identity[Unit])
      val lhs    = idUnit >>> p
      assert(lhs.run(st) === p.run(st))
    }
  }

  test("Promonad: Parser right unitality") {
    val p = PA.literal("xyz")
    forAll { (st: ParserState) =>
      val idStr = ProM.unit(identity[String])
      val lhs   = p >>> idStr
      assert(lhs.run(st) === p.run(st))
    }
  }

  test("Promonad: Parser associativity") {
    val p1: Parser[Unit, String]   = PA.literal("1")
    val p2: Parser[String, String] = PA.literal("2").lmap((_: String) => ())
    val p3: Parser[String, String] = PA.literal("3").lmap((_: String) => ())
    forAll { (st: ParserState) =>
      val lhs = (p1 >>> p2) >>> p3
      val rhs = p1 >>> (p2 >>> p3)
      assert(lhs.run(st) === rhs.run(st))
    }
  }

  // =========================================================================
  // PromonoidPlus Laws on Parser
  // =========================================================================

  test("PromonoidPlus: Parser left identity") {
    val p = PA.literal("abc")
    forAll { (st: ParserState) =>
      val lhs = PMP.zero[Unit, String] <+> p
      assert(lhs.run(st) === p.run(st))
    }
  }

  test("PromonoidPlus: Parser right identity (up to failure equivalence)") {
    val p = PA.literal("abc")
    forAll { (st: ParserState) =>
      val lhs = p <+> PMP.zero[Unit, String]
      assert(lhs.run(st) =~= p.run(st))
    }
  }

  test("PromonoidPlus: Parser associativity") {
    val p1 = PA.literal("a")
    val p2 = PA.literal("b")
    val p3 = PA.literal("c")
    forAll { (st: ParserState) =>
      val lhs = (p1 <+> p2) <+> p3
      val rhs = p1 <+> (p2 <+> p3)
      assert(lhs.run(st) === rhs.run(st))
    }
  }

  // =========================================================================
  // CartesianStrongProfunctor and CocartesianStrongProfunctor Laws on Parser
  // =========================================================================

  test("CartesianStrongProfunctor: Parser unitality") {
    val p    = PA.literal("a")
    val self = p.first[Unit].dimap((a: Unit) => (a, ()), { case (b, _) => b })
    forAll { (st: ParserState) =>
      assert(self.run(st) === p.run(st))
    }
  }

  test("CartesianStrongProfunctor: Parser associativity") {
    val p                                                   = PA.literal("a")
    val f: ((Unit, (String, Int))) => ((Unit, String), Int) =
      in => ((in._1, in._2._1), in._2._2)
    val g: (((String, String), Int)) => (String, (String, Int)) =
      out => (out._1._1, (out._1._2, out._2))

    val lhs = p.first[String].first[Int].dimap(f, g)
    val rhs = p.first[(String, Int)]

    forAll { (st: ParserState) =>
      val input: (Unit, (String, Int)) = ((), ("s", 42))
      assert(lhs.run(input, st) === rhs.run(input, st))
    }
  }

  test("CocartesianStrongProfunctor: Parser unitality") {
    val p                                    = PA.literal("a")
    val f: Unit => Either[Unit, Nothing]     = Left(_)
    val g: Either[String, Nothing] => String = _.merge
    val self                                 = p.left[Nothing].dimap(f, g)
    forAll { (st: ParserState) =>
      assert(self.run(st) === p.run(st))
    }
  }

  test("CocartesianStrongProfunctor: Parser associativity") {
    val p = PA.literal("a")

    val f: Either[Unit, Either[String, Int]] => Either[Either[Unit, String], Int] = {
      case Left(u)         => Left(Left(u))
      case Right(Left(s))  => Left(Right(s))
      case Right(Right(i)) => Right(i)
    }
    val g: Either[Either[String, String], Int] => Either[String, Either[String, Int]] = {
      case Left(Left(s1))  => Left(s1)
      case Left(Right(s2)) => Right(Left(s2))
      case Right(i)        => Right(Right(i))
    }

    val lhs = p.left[String].left[Int].dimap(f, g)
    val rhs = p.left[Either[String, Int]]

    forAll { (st: ParserState) =>
      val in1: Either[Unit, Either[String, Int]] = Left(())
      val in2: Either[Unit, Either[String, Int]] = Right(Left("c"))
      val in3: Either[Unit, Either[String, Int]] = Right(Right(42))
      assert(
        (lhs.run(in1, st) === rhs.run(in1, st)) &&
          (lhs.run(in2, st) === rhs.run(in2, st)) &&
          (lhs.run(in3, st) === rhs.run(in3, st)),
      )
    }
  }

  // =========================================================================
  // CartesianMonoidalProfunctor Laws on Parser
  // =========================================================================

  test("CartesianMonoidalProfunctor: Parser left identity") {
    val p   = PA.literal("x")
    val lhs = (MP.unit *** p).dimap(
      (a: Unit) => ((), a),
      (_, b: String) => b,
    )
    forAll { (st: ParserState) =>
      assert(lhs.run(st) === p.run(st))
    }
  }

  test("CartesianMonoidalProfunctor: Parser right identity") {
    val p   = PA.literal("x")
    val lhs = (p *** MP.unit).dimap(
      (a: Unit) => (a, ()),
      (b: String, _) => b,
    )
    forAll { (st: ParserState) =>
      assert(lhs.run(st) === p.run(st))
    }
  }

  test("CartesianMonoidalProfunctor: Parser associativity") {
    val p1 = PA.literal("1")
    val p2 = PA.literal("2")
    val p3 = PA.literal("3")

    val lhs = ((p1 *** p2) *** p3).dimap(
      (in: (Unit, (Unit, Unit))) => ((in._1, in._2._1), in._2._2),
      (out: ((String, String), String)) => (out._1._1, (out._1._2, out._2)),
    )
    val rhs = p1 *** (p2 *** p3)

    forAll { (st: ParserState) =>
      val input: (Unit, (Unit, Unit)) = ((), ((), ()))
      assert(lhs.run(input, st) === rhs.run(input, st))
    }
  }

  // =========================================================================
  // RestrictionPromonad Laws on Parser
  // =========================================================================

  test("RestrictionPromonad: Parser restriction law") {
    val p                         = PA.literal("test")
    val lhs: Parser[Unit, String] = p.restrict >>> p
    forAll { (st: ParserState) =>
      assert(lhs.run(st) === p.run(st))
    }
  }

  test("RestrictionPromonad: Parser commutativity law (up to failure equivalence)") {
    val p: Parser[Unit, String] = PA.literal("a")
    val q: Parser[Unit, String] = PA.literal("b")
    forAll { (st: ParserState) =>
      val lhs: Parser[Unit, Unit] = p.restrict >>> q.restrict
      val rhs: Parser[Unit, Unit] = q.restrict >>> p.restrict
      assert(lhs.run(st) =~= rhs.run(st))
    }
  }

  test("RestrictionPromonad: Parser absorption law (up to failure equivalence)") {
    val p: Parser[Unit, String] = PA.literal("a")
    val q: Parser[Unit, String] = PA.literal("b")
    forAll { (st: ParserState) =>
      val lhs: Parser[Unit, Unit] = (p.restrict >>> q).restrict
      val rhs: Parser[Unit, Unit] = p.restrict >>> q.restrict
      assert(lhs.run(st) =~= rhs.run(st))
    }
  }

  test("RestrictionPromonad: Parser lax naturality law (up to failure equivalence)") {
    val p: Parser[Unit, String]   = PA.literal("a")
    val q: Parser[String, String] = PA.literal("b").lmap((_: String) => ())
    forAll { (st: ParserState) =>
      val lhs: Parser[Unit, String] = p >>> q.restrict
      val rhs: Parser[Unit, String] = (p >>> q).restrict >>> p
      assert(lhs.run(st) =~= rhs.run(st))
    }
  }

  // =========================================================================
  // ElgotPromonad Laws on Parser
  // =========================================================================

  test("ElgotPromonad: Parser fixpoint law") {
    val p: Parser[Int, Either[String, Int]] = (x: Int) =>
      state =>
        if x <= 0 then Success((result = Left(x.toString), state = state))
        else if state.tokens.isEmpty then Failure(Exception("empty state"))
        else Success((result = Right(x - 1), state = (memo = state.memo, tokens = state.tokens.drop(1))))

    val lhs = p.dagger
    val rhs = p >>> p.dagger.right[String] >>> ProM.unit(_.merge)

    forAll { (n: Int, st: ParserState) =>
      assert(lhs.run(n, st) === rhs.run(n, st))
    }
  }

  test("ElgotPromonad: Parser naturality in parameters law") {
    val p: Parser[Int, Either[Int, Int]] = (x: Int) =>
      state =>
        if x <= 0 then Success((result = Left(x), state = state))
        else if state.tokens.isEmpty then Failure(Exception("empty state"))
        else Success((result = Right(x - 1), state = (memo = state.memo, tokens = state.tokens.drop(1))))
    val g: Int => String = _.toString

    val lhs = p.dagger >>> ProM.unit(g)
    val rhs = (p >>> ProM.unit(_.left.map(g))).dagger

    forAll { (n: Int, st: ParserState) =>
      assert(lhs.run(n, st) === rhs.run(n, st))
    }
  }

  test("ElgotPromonad: Parser dinaturality law") {
    val p: Parser[Int, Either[String, Int]] = (x: Int) =>
      state =>
        if x <= 0 then Success((result = Left(x.toString), state = state))
        else if state.tokens.isEmpty then Failure(Exception("empty state"))
        else Success((result = Right(x), state = (memo = state.memo, tokens = state.tokens.drop(1))))
    val g: Int => Int = c => c - 1

    val lhs = (p >>> ProM.unit(_.map(g))).dagger
    val rhs = p >>> (ProM.unit(g) >>> p).dagger.right[String] >>> ProM.unit(_.merge)

    forAll { (n: Int, st: ParserState) =>
      assert(lhs.run(n, st) === rhs.run(n, st))
    }
  }

  test("ElgotPromonad: Parser codiagonal law") {
    val p: Parser[Int, Either[Either[String, Int], Int]] = (x: Int) =>
      state =>
        if x <= 0 then Success((result = Left(Left(x.toString)), state = state))
        else if state.tokens.isEmpty then Failure(Exception("empty state"))
        else if x % 2 == 0 then
          Success((result = Left(Right(x - 2)), state = (memo = state.memo, tokens = state.tokens.drop(1))))
        else Success((result = Right(x - 1), state = (memo = state.memo, tokens = state.tokens.drop(1))))

    val lhs = p.dagger.dagger
    val rhs =
      (p >>> ProM.unit {
        case Left(Left(b))  => Left(b)
        case Left(Right(a)) => Right(a)
        case Right(a)       => Right(a)
      }).dagger

    forAll { (n: Int, st: ParserState) =>
      assert(lhs.run(n, st) === rhs.run(n, st))
    }
  }

  test("ElgotPromonad: Parser uniformity law") {
    val h: Int => Int                       = _ + 1
    val q: Parser[Int, Either[String, Int]] = (y: Int) =>
      state =>
        if y <= 0 then Success((result = Left(y.toString), state = state))
        else if state.tokens.isEmpty then Failure(Exception("empty state"))
        else Success((result = Right(y - 2), state = (memo = state.memo, tokens = state.tokens.drop(1))))

    val p: Parser[Int, Either[String, Int]] = (a: Int) =>
      state =>
        q(h(a))(state).map { res => (result = res.result.map(y => y - 1), state = res.state) }

    val lhs = p.dagger
    val rhs = ProM.unit(h) >>> q.dagger

    forAll { (n: Int, st: ParserState) =>
      assert(lhs.run(n, st) === rhs.run(n, st))
    }
  }
}
