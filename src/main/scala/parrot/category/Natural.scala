package parrot
package category

/** A natural transformation *α*: *F* ⇒ *G* between functors *F*, *G*: **C** → **D**.
  *
  * Represents a family of morphisms of **D**, where
  *   - *α*_*A*: *F*[*A*] → *G*[*A*] is the component at an object *A* of **C**
  *
  * The components commute with the morphisms of **C**.
  *
  * @see docs/TUTORIAL.md §13.2
  */
abstract class Natural(
  tracked val functor1: Functor,
  tracked val functor2: Functor { val source: functor1.source.type; val target: functor1.target.type },
) extends caps.Pure {
  import functor1.source as C
  import functor1.target as D
  import functor1.F
  import functor2.F as G
  import C.-->
  import D.--> as ==>

  /** The component *α*_*A*: *F*[*A*] → *G*[*A*]. */
  def component[A: C.Obj]: F[A] ==> G[A]

  /** Laws that any `Natural` transformation must satisfy. */
  object NaturalLaws {
    private given FIsObj: [A: C.Obj] => (F[A] is D.Obj) = functor1.objects[A]
    private given GIsObj: [A: C.Obj] => (G[A] is D.Obj) = functor2.objects[A]

    /** *α*_*B* ∘ *F*(*f*) = *G*(*f*) ∘ *α*_*A*
      */
    def naturality[A: C.Obj, B: C.Obj](f: A --> B)(using (F[A] ==> G[B]) is Observable): Boolean = {
      (functor1.map(f) >>> component[B]) =?= (component[A] >>> functor2.map(f))
    }
  }
}

object Natural {

  /** The natural transformations out of a functor *F*. */
  type From[F <: Functor] = Natural { val functor1: F }
}
