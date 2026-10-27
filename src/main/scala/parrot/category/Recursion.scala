package parrot
package category

/** Recursion at the arrow types of a promonad: a fixed point for every function from arrows to arrows.
  *
  * Represents a fixed-point operator on the objects *P*(*A*,*B*) of 𝒮, where
  *   - *fix*(*f*) = *f*(*fix*(*f*)) for *f*: *P*(*A*,*B*) → *P*(*A*,*B*)
  *   - *fixFamily*(*n*,*f*) = *f*(*fixFamily*(*n*,*f*)) for *f* on families of *n* arrows: mutual recursion
  *
  * A family could be solved one arrow at a time, by Bekić's theorem, but that applies *f* exponentially often in *n*;
  * instances solve it at once, with one knot per arrow.
  *
  * These are fixed points in 𝒮 at function types, not a structure of the category of arrows: a grammar rule refers to
  * itself as a value. In 𝒫 they exist for every *f* ([[Partial.Knots]]): the arrow types of 𝒫 contain the
  * nowhere-terminating program, which is the least solution. In 𝒮 they exist for guarded *f*, which use their argument
  * only after making progress; a total instance stops with failure where *f* would recurse without progress, so the law
  * holds for guarded *f* only.
  */
abstract class Recursion(tracked val P: Promonad) extends caps.Pure {
  import P.P
  import P.K.Obj

  /** The fixed point *fix*(*f*) of *f*: *P*(*A*,*B*) → *P*(*A*,*B*). */
  def fix[A: Obj, B: Obj](f: P[A, B] -> P[A, B]): P[A, B]

  /** The fixed point of *f* on families of *n* arrows *P*(*A*,*B*), indexed by `0 until n`: *n* arrows that may refer
    * to each other.
    */
  def fixFamily[A: Obj, B: Obj](n: Int)(f: (Int -> P[A, B]) -> Int -> P[A, B]): Int -> P[A, B]

  /** Laws that any `Recursion` must satisfy. */
  object RecursionLaws {

    /** *fix*(*f*) = *f*(*fix*(*f*))
      */
    def fixedPoint[A: Obj, B: Obj](f: P[A, B] -> P[A, B])(
      using P[A, B] is Observable
    ): Boolean = {
      fix(f) =?= f(fix(f))
    }

    /** *fixFamily*(*n*,*f*)(*i*) = *f*(*fixFamily*(*n*,*f*))(*i*) for every *i* < *n*
      */
    def familyFixedPoint[A: Obj, B: Obj](n: Int)(f: (Int -> P[A, B]) -> Int -> P[A, B])(
      using P[A, B] is Observable
    ): Boolean = {
      val solved = fixFamily(n)(f)
      (0 until n).forall(i => solved(i) =?= f(solved)(i))
    }
  }
}
