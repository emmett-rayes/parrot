package parrot
package category

/** A cone over a diagram *D*: **J** → **C**.
  *
  * Represents a cone (*X*, *ψ*), where
  *   - *X* is the apex, an object of **C**
  *   - *ψ*_*A*: *X* → *D*[*A*] is the leg at an object *A* of **J**
  */
abstract class Cone(tracked val diagram: Functor, tracked val apex: diagram.target.Object) extends caps.Pure {
  import diagram.{F as D, map}
  import diagram.source as J
  import diagram.target as C
  import J.-->
  import C.--> as ==>

  /** The apex *X*. */
  final type X = apex.A

  private given XIsObj: X is C.Obj                    = apex.evidence
  private given DIsObj: [A: J.Obj] => (D[A] is C.Obj) = diagram.objects[A]

  /** *ψ*_*A*: *X* → *D*[*A*]
    *
    * The legs form a natural transformation from the constant functor at *X* to *D*.
    */
  def leg[A: J.Obj]: X ==> D[A]

  /** The cone (*Y*, *ψ* ∘ *h*) induced by a morphism *h*: *Y* → *X*. */
  final def induced[Y: C.Obj](h: Y ==> X): Cone.Of[diagram.type] { val apex: C.ObjectOf[Y] } = {
    new Cone(diagram, C.Object[Y]) {
      def leg[A: J.Obj]: Y ==> D[A] = {
        h >>> Cone.this.leg[A]
      }
    }
  }

  /** Laws that any `Cone` must satisfy. */
  object ConeLaws {

    /** *D*(*f*) ∘ *ψ*_*A* = *ψ*_*B*
      */
    def commutes[A: J.Obj, B: J.Obj](f: A --> B)(using (X ==> D[B]) is Observable): Boolean = {
      (leg[A] >>> map(f)) =?= leg[B]
    }
  }
}

object Cone {

  /** Refines `Cone` to a specific functor **F**. */
  type Of[F <: Functor] = Cone { val diagram: F }
}
