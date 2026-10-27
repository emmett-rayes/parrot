package parrot
package parser

import category.*

/** Reified pure functions: the morphisms of [[Fns]], a category equivalent to 𝒮 on the types used by parsers.
  *
  * Structural morphisms (identities, projections, injections, pairings, and copairings) are kept as data rather than
  * closures so that interpreters can inspect and simplify them at construction time. Composition, pairing and copairing
  * are smart constructors that simplify with the equations of a category with finite products and coproducts, and
  * associate composites to the right:
  *   - *id* ⨾ *f* = *f* = *f* ⨾ *id*
  *   - ⟨*f*,*g*⟩ ⨾ *π*₁ = *f*, ⟨*f*,*g*⟩ ⨾ *π*₂ = *g*, ⟨*π*₁,*π*₂⟩ = *id*
  *   - *ι*₁ ⨾ [*f*,*g*] = *f*, *ι*₂ ⨾ [*f*,*g*] = *g*, [*ι*₁,*ι*₂] = *id*
  *   - *f* ⨾ ! = !
  *   - adjacent lifted functions are fused into one
  *
  * The result is simpler, not a normal form: equal morphisms can have different representations.
  *
  * @note Lifted functions must be total and pure, as befits morphisms of the base category; normalization may discard
  *   or fuse them.
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
  final case class Lift[A, B](f: A -> B) extends Fn[A, B] {
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
  def lift[A, B](f: A -> B): Fn[A, B] = Lift(f)

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
      case (Lift(f1), Lift(g1))     => Lift(a => g1(f1(a)))
      case (Compose(f1, f2), _)     => compose(f1, compose(f2, g))
      case _                        => Compose(f, g)
    }
  }
}

/** The category of reified pure functions, with objects all types.
  *
  * Represents a category equivalent to 𝒮 on the types it is used with, where
  *   - *id* = `Fn.Id` and ∘ is the normalizing composition of [[Fn.andThen]]
  *   - [[Product]] and [[Coproduct]] are reified, so that parsers can inspect them
  */
object Fns extends Category {
  type Self = Fn
  type Obj  = Type

  def identity[A: Type]: Fn[A, A] = {
    Fn.id
  }

  def compose[A: Type, B: Type, C: Type](g: Fn[B, C], f: Fn[A, B]): Fn[A, C] = {
    Fn.andThen(f, g)
  }

  /** Pairs as a bifunctor on [[Fns]]. */
  object Tuple2IsBifunctor extends Bifunctor(Fns, Fns, Fns) {
    type Self = Tuple2

    def objects[A: Type, B: Type]: (A, B) is Type = {
      Type.TIsType
    }

    def bimap[A: Type, B: Type, A2: Type, B2: Type](f: Fn[A, A2], g: Fn[B, B2]): Fn[(A, B), (A2, B2)] = {
      Fn.fanout(Fn.andThen(Fn.Proj1(), f), Fn.andThen(Fn.Proj2(), g))
    }
  }

  /** Tagged unions as a bifunctor on [[Fns]]. */
  object EitherIsBifunctor extends Bifunctor(Fns, Fns, Fns) {
    type Self = Either

    def objects[A: Type, B: Type]: Either[A, B] is Type = {
      Type.TIsType
    }

    def bimap[A: Type, B: Type, A2: Type, B2: Type](f: Fn[A, A2], g: Fn[B, B2]): Fn[Either[A, B], Either[A2, B2]] = {
      Fn.copair(Fn.andThen(f, Fn.Inl()), Fn.andThen(g, Fn.Inr()))
    }
  }

  /** Reified products: pairs, with projections and pairing as data. */
  object Product extends Cartesian(Fns, Tuple2IsBifunctor) {
    type I = Unit

    def unitObject: Unit is Type = {
      Type.TIsType
    }

    def fst[A: Type, B: Type]: Fn[(A, B), A] = {
      Fn.Proj1()
    }

    def snd[A: Type, B: Type]: Fn[(A, B), B] = {
      Fn.Proj2()
    }

    def pair[X: Type, A: Type, B: Type](f: Fn[X, A], g: Fn[X, B]): Fn[X, (A, B)] = {
      Fn.fanout(f, g)
    }

    def discard[A: Type]: Fn[A, Unit] = {
      Fn.Bang()
    }
  }

  /** Reified coproducts: `Either`, with injections and copairing as data. */
  object Coproduct extends Cocartesian(Fns, EitherIsBifunctor) {
    type I = Nothing

    def unitObject: Nothing is Type = {
      Type.TIsType
    }

    def inl[A: Type, B: Type]: Fn[A, Either[A, B]] = {
      Fn.Inl()
    }

    def inr[A: Type, B: Type]: Fn[B, Either[A, B]] = {
      Fn.Inr()
    }

    def copair[A: Type, B: Type, X: Type](f: Fn[A, X], g: Fn[B, X]): Fn[Either[A, B], X] = {
      Fn.copair(f, g)
    }

    def absurd[A: Type]: Fn[Nothing, A] = {
      Fn.Absurd()
    }
  }
}
