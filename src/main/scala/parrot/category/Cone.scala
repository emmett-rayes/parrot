package parrot
package category

/** A cone over a diagram *D*: **J** → **C**.
  *
  * Represents a cone (*X*, *ψ*), where
  *   - *X* is the apex, an object of **C**
  *   - *ψ*_*A*: *X* → *D*[*A*] is the leg at an object *A* of **J**
  */
abstract class Cone(tracked val D: Functor) extends caps.Pure {
  import D.{F, map}
  import D.C as J
  import D.D as C
  import J.-->
  import C.--> as ==>

  /** The apex *X*. */
  type Apex

  /** Evidence that *X* is an object of **C**. */
  def apex: Apex is C.Obj

  private given ApexIsObj: Apex is C.Obj = apex

  private given FIsObj: [A: J.Obj] => (F[A] is C.Obj) = D.objects[A]

  /** *ψ*_*A*: *X* → *D*[*A*]
    *
    * The legs form a natural transformation from the constant functor at *X* to *D*.
    */
  def leg[A: J.Obj]: Apex ==> F[A]

  /** The cone (*Y*, *ψ* ∘ *h*) induced by a morphism *h*: *Y* → *X*. */
  final def induced[Y: C.Obj as obj](h: Y ==> Apex): Cone { val D: Cone.this.D.type; type Apex = Y } = {
    new Cone(D) {
      type Apex = Y
      def apex: Y is C.Obj             = obj
      def leg[A: J.Obj]: Apex ==> F[A] = h >>> Cone.this.leg[A]
    }
  }

  /** Laws that any `Cone` must satisfy. */
  object ConeLaws {

    /** *D*(*f*) ∘ *ψ*_*A* = *ψ*_*B*
      */
    def commutes[A: J.Obj, B: J.Obj](f: A --> B)(using (Apex ==> F[B]) is Observable): Boolean = {
      (leg[A] >>> map(f)) =?= leg[B]
    }
  }
}
