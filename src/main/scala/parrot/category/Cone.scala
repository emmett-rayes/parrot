package parrot
package category

/** A cone over a diagram *D*: **J** → **C**.
  *
  * Represents a cone (*X*, *ψ*), where
  *   - *X* is the apex, an object of **C**
  *   - *ψ*_*A*: *X* → *D*[*A*] is the leg at an object *A* of **J**
  */
abstract class Cone(tracked val D: Functor, tracked val X: D.D.Obj) extends caps.Pure {
  import D.{F as D, map}
  import D.C as J
  import D.D as C
  import J.-->
  import C.--> as ==>

  /** The apex *X*. */
  final type Apex = X.Self

  private given ApexIsObj: Apex is C.Obj              = X
  private given DIsObj: [A: J.Obj] => (D[A] is C.Obj) = D.objects[A]

  /** *ψ*_*A*: *X* → *D*[*A*]
    *
    * The legs form a natural transformation from the constant functor at *X* to *D*.
    */
  def leg[A: J.Obj]: Apex ==> D[A]

  /** The cone (*Y*, *ψ* ∘ *h*) induced by a morphism *h*: *Y* → *X*. */
  final def induced[Y: C.Obj as obj](h: Y ==> Apex): Cone.Of[D.type] { val X: obj.type } = {
    new Cone(D, obj) {
      def leg[A: J.Obj]: Y ==> D[A] = {
        h >>> Cone.this.leg[A]
      }
    }
  }

  /** Laws that any `Cone` must satisfy. */
  object ConeLaws {

    /** *D*(*f*) ∘ *ψ*_*A* = *ψ*_*B*
      */
    def commutes[A: J.Obj, B: J.Obj](f: A --> B)(using (Apex ==> D[B]) is Observable): Boolean = {
      (leg[A] >>> map(f)) =?= leg[B]
    }
  }
}

object Cone {

  /** Refines `Cone` to a specific functor **F**. */
  type Of[F <: Functor] = Cone { val D: F }
}
