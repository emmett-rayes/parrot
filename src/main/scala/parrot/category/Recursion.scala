package parrot
package category

/** A recursion structure on a promonad *P* over **C**.
  *
  * Represents fixed points at the types of the arrows of *P*, where
  *   - *fix*: (*P*(*A*,*B*) → *P*(*A*,*B*)) → *P*(*A*,*B*) is the fixed-point operator.
  *   - *fixFamily*: (*P*(*A*,*B*)ⁿ → *P*(*A*,*B*)ⁿ) → *P*(*A*,*B*)ⁿ is the fixed-point operator on a family of *n*
  *     arrows.
  */
abstract class Recursion(tracked val promonad: Promonad) extends caps.Pure {
  import promonad.arrows.-->
  import promonad.category.Obj

  /** The fixed point *fix*(*f*): *P*(*A*,*B*) of *f*: *P*(*A*,*B*) → *P*(*A*,*B*).
    *
    * It solves *p* = *f*(*p*) for the arrow *p*.
    */
  def fix[A: Obj, B: Obj](f: (A --> B) -> (A --> B)): A --> B

  /** The fixed point *fixFamily*(*n*,*f*): *P*(*A*,*B*)ⁿ of *f*: *P*(*A*,*B*)ⁿ → *P*(*A*,*B*)ⁿ.
    *
    * It solves *p*ᵢ = *f*(*p*)ᵢ for the arrows *p*ᵢ of a family indexed by 0 ≤ *i* < *n*.
    */
  def fixFamily[A: Obj, B: Obj](n: Int)(f: (Int -> (A --> B)) -> Int -> (A --> B)): Int -> (A --> B) = {
    bekic(n)(f)
  }

  /** The fixed point of *f*: *P*(*A*,*B*)ⁿ → *P*(*A*,*B*)ⁿ by Bekić's theorem, with *fix* only.
    *
    * The arrow *p*ₖ is *fix*(*x* ↦ *f*(*q*)ₖ), where *q* puts *x* at *k*, the solved *p*ᵢ at *i* < *k*, and the arrows
    * at *i* > *k* solved in the same way, given *x*. This applies *f* exponentially often in *n*.
    *
    * @note Indices outside 0 ≤ *i* < *n* are unconstrained: they get *fix*(*id*).
    */
  private def bekic[A: Obj, B: Obj](n: Int)(f: (Int -> (A --> B)) -> Int -> (A --> B)): Int -> (A --> B) = {
    def solve(k: Int, family: Int -> (A --> B)): Int -> (A --> B) = {
      if k >= n then family
      else {
        def at(p: A --> B): Int -> (A --> B) = i => if i == k then p else family(i)
        val solved                           = fix[A, B](x => f(solve(k + 1, at(x)))(k))
        solve(k + 1, at(solved))
      }
    }
    solve(0, _ => fix[A, B](p => p))
  }

  /** Laws that any `Recursion` structure must satisfy. */
  object RecursionLaws {

    /** *fix*(*f*) = *f*(*fix*(*f*))
      *
      * Unfolding one step changes nothing.
      */
    def fixedPoint[A: Obj, B: Obj](f: (A --> B) -> (A --> B))(using (A --> B) is Observable): Boolean = {
      fix(f) =?= f(fix(f))
    }

    /** *fixFamily*(*n*,*f*)ᵢ = *f*(*fixFamily*(*n*,*f*))ᵢ for 0 ≤ *i* < *n*
      *
      * Unfolding one step of every arrow of the family changes nothing.
      */
    def familyFixedPoint[A: Obj, B: Obj](n: Int)(f: (Int -> (A --> B)) -> Int -> (A --> B))(
      using (A --> B) is Observable
    ): Boolean = {
      val solved = fixFamily(n)(f)
      (0 until n).forall(i => solved(i) =?= f(solved)(i))
    }

    /** *fixFamily*(*n*,*f*)ᵢ = *bekic*(*n*,*f*)ᵢ for 0 ≤ *i* < *n*
      *
      * Solving a family at once agrees with solving it one arrow at a time.
      */
    def fixFamilyIsBekic[A: Obj, B: Obj](n: Int)(f: (Int -> (A --> B)) -> Int -> (A --> B))(
      using (A --> B) is Observable
    ): Boolean = {
      val solved = fixFamily(n)(f)
      val nested = bekic(n)(f)
      (0 until n).forall(i => solved(i) =?= nested(i))
    }
  }
}

object Recursion {

  /** The recursion structures on a promonad *P*. */
  type On[P <: Promonad] = Recursion { val promonad: P }
}
