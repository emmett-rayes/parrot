package parrot
package parser

import category.{Cartesian, Cocartesian, Promonad}

/** Reified morphisms of the base category **Type** (with ×, `Unit`, `Either`, `Nothing`).
  *
  * Structural morphisms (identities, projections, injections, pairings, and copairings) are kept as data rather than
  * closures so that interpreters can inspect and normalize them at construction time. Composition is a smart
  * constructor that rewrites to normal form using the equations of a distributive category:
  *   - *id* ⨾ *f* = *f* = *f* ⨾ *id*
  *   - ⟨*f*, *g*⟩ ⨾ *π*₁ = *f*, ⟨*f*, *g*⟩ ⨾ *π*₂ = *g*, ⟨*π*₁, *π*₂⟩ = *id*
  *   - *ι*₁ ⨾ [*f*, *g*] = *f*, *ι*₂ ⨾ [*f*, *g*] = *g*, [*ι*₁, *ι*₂] = *id*
  *   - *f* ⨾ ! = !
  *
  * @note
  *   Lifted functions must be total and pure, as befits morphisms of the base category; normalization may discard or
  *   fuse them.
  */
sealed trait Fn[A, B] {

  /** Applies this reified morphism to `a`. */
  def apply(a: A): B
}

object Fn {

  /** The identity morphism *id*: *A* → *A*. */
  final case class Id[A]() extends Fn[A, A] {
    def apply(a: A): A = a
  }

  /** An opaque lifted Scala function *f*: *A* → *B*. */
  final case class Lift[A, B](f: A => B) extends Fn[A, B] {
    def apply(a: A): B = f(a)
  }

  /** The sequential composition *f* ⨾ *g*: *A* → *C*. */
  final case class Compose[A, B, C](f: Fn[A, B], g: Fn[B, C]) extends Fn[A, C] {
    def apply(a: A): C = g(f(a))
  }

  /** The unique morphism !: *A* → `Unit` to the terminal object. */
  final case class Bang[A]() extends Fn[A, Unit] {
    def apply(a: A): Unit = ()
  }

  /** The first projection morphism *π*₁: *A* × *B* → *A*. */
  final case class Proj1[A, B]() extends Fn[(A, B), A] {
    def apply(ab: (A, B)): A = ab._1
  }

  /** The second projection morphism *π*₂: *A* × *B* → *B*. */
  final case class Proj2[A, B]() extends Fn[(A, B), B] {
    def apply(ab: (A, B)): B = ab._2
  }

  /** The universal pairing morphism ⟨*f*, *g*⟩: *A* → *B* × *C*. */
  final case class Fanout[A, B, C](f: Fn[A, B], g: Fn[A, C]) extends Fn[A, (B, C)] {
    def apply(a: A): (B, C) = (f(a), g(a))
  }

  /** The unique morphism ¡: `Nothing` → *A* from the initial object. */
  final case class Absurd[A]() extends Fn[Nothing, A] {
    def apply(a: Nothing): A = a
  }

  /** The left injection morphism *ι*₁: *A* → `Either`[*A*, *B*]. */
  final case class Inl[A, B]() extends Fn[A, Either[A, B]] {
    def apply(a: A): Either[A, B] = Left(a)
  }

  /** The right injection morphism *ι*₂: *B* → `Either`[*A*, *B*]. */
  final case class Inr[A, B]() extends Fn[B, Either[A, B]] {
    def apply(b: B): Either[A, B] = Right(b)
  }

  /** The universal copairing morphism [*f*, *g*]: `Either`[*A*, *B*] → *C*. */
  final case class Copair[A, B, C](f: Fn[A, C], g: Fn[B, C]) extends Fn[Either[A, B], C] {
    def apply(ab: Either[A, B]): C = ab.fold(f.apply, g.apply)
  }

  /** The identity morphism *id*: *A* → *A*. */
  def id[A]: Fn[A, A] = Id()

  /** Lifts a pure Scala function `f` into [[Fn]]. */
  def lift[A, B](f: A => B): Fn[A, B] = Lift(f)

  /** Normalizing composition *f* ⨾ *g*. */
  def andThen[A, B, C](f: Fn[A, B], g: Fn[B, C]): Fn[A, C] = {
    compose(f, g)
  }

  /** Normalizing pairing ⟨*f*, *g*⟩. */
  def fanout[A, B, C](f: Fn[A, B], g: Fn[A, C]): Fn[A, (B, C)] = {
    (f, g) match {
      case (Proj1(), Proj2()) => Id()
      case _                  => Fanout(f, g)
    }
  }

  /** Normalizing copairing [*f*, *g*]. */
  def copair[A, B, C](f: Fn[A, C], g: Fn[B, C]): Fn[Either[A, B], C] = {
    (f, g) match {
      case (Inl(), Inr()) => Id()
      case _              => Copair(f, g)
    }
  }

  private def compose[A, B, C](f: Fn[A, B], g: Fn[B, C]): Fn[A, C] = {
    (f, g) match {
      case (Id(), _)                => g
      case (_, Id())                => f
      case (_, Bang())              => Bang()
      case (Fanout(f1, _), Proj1()) => f1
      case (Fanout(_, f2), Proj2()) => f2
      case (Inl(), Copair(g1, _))   => g1
      case (Inr(), Copair(_, g2))   => g2
      case (Lift(f1), Lift(g1))     => Lift(f1.andThen(g1))
      case (Compose(f1, f2), _)     => compose(f1, compose(f2, g))
      case _                        => Compose(f, g)
    }
  }

  /** `Fn` is a promonad on **Type**, embedding functions as opaque lifts. */
  given FnIsPromonad: Fn is Promonad {
    type On = Function

    override given ProfunctorOnPromonad: (Function is Promonad) = Promonad.FunctionIsPromonad
    override val OnIsPromonad: Promonad.FunctionIsPromonad.type = Promonad.FunctionIsPromonad

    def unit[A, B](f: A => B): Fn[A, B] = Fn.lift(f)

    def multiply[A, B, C](q: Fn[B, C], p: Fn[A, B]): Fn[A, C] = Fn.andThen(p, q)

    override def identity[A]: Fn[A, A] = Fn.id
  }

  /** `Fn` is cartesian under (`Tuple2`, `Unit`) with reified projections and pairing. */
  given FnIsCartesian: Fn is Cartesian {
    type I      = Unit
    type Tensor = Tuple2

    def augment[A]: Fn[A, Unit] = Bang()

    def first[A, B]: Fn[(A, B), A] = Proj1()

    def second[A, B]: Fn[(A, B), B] = Proj2()

    def product[C, A, B](f: Fn[C, A], g: Fn[C, B]): Fn[C, (A, B)] = Fn.fanout(f, g)
  }

  /** `Fn` is cocartesian under (`Either`, `Nothing`) with reified injections and copairing. */
  given FnIsCocartesian: Fn is Cocartesian {
    type Z      = Nothing
    type Tensor = Either

    def absurd[A]: Fn[Nothing, A] = Absurd()

    def left[A, B]: Fn[A, Either[A, B]] = Inl()

    def right[A, B]: Fn[B, Either[A, B]] = Inr()

    def sum[A, B, C](f: Fn[A, C], g: Fn[B, C]): Fn[Either[A, B], C] = Fn.copair(f, g)
  }
}
