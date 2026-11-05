package parrot
package category

/** A cocone under a diagram *D*: **J** → **C**.
  *
  * Represents a cocone (*X*, *ψ*), where
  *   - *X* is the apex, an object of **C**
  *   - *ψ*_*A*: *D*[*A*] → *X* is the leg at an object *A* of **J**
  */
abstract class Cocone(tracked val diagram: Functor, tracked val apex: diagram.target.Object) extends caps.Pure {
  import diagram.{F as D, map}
  import diagram.source as J
  import diagram.target as C
  import J.-->
  import C.--> as ==>

  /** The apex *X*. */
  final type X = apex.A

  /** *ψ*_*A*: *D*[*A*] → *X*
    *
    * The legs form a natural transformation from *D* to the constant functor at *X*.
    */
  def leg[A: J.Obj]: D[A] ==> X

  private given XIsObj: X is C.Obj                    = apex.evidence
  private given DIsObj: [A: J.Obj] => (D[A] is C.Obj) = diagram.objects[A]

  /** The cocone (*Y*, *h* ∘ *ψ*) induced by a morphism *h*: *X* → *Y*. */
  final def induced[Y: C.Obj](h: X ==> Y): Cocone.Under[diagram.type] { val apex: Y is C.Object } = {
    new Cocone(diagram, C.Object[Y]) {
      def leg[A: J.Obj]: D[A] ==> Y = {
        Cocone.this.leg[A] >>> h
      }
    }
  }

  /** Laws that any `Cocone` must satisfy. */
  object CoconeLaws {

    /** *ψ*_*B* ∘ *D*(*f*) = *ψ*_*A*
      */
    def commutes[A: J.Obj, B: J.Obj](f: A --> B)(using (D[A] ==> X) is Observable): Boolean = {
      (map(f) >>> leg[B]) =?= leg[A]
    }
  }
}

object Cocone {

  /** The cocones under a diagram *D*. */
  type Under[D <: Functor] = Cocone { val diagram: D }
}
