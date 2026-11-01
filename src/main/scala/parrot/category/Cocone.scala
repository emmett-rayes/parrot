package parrot
package category

/** A cocone under a diagram *D*: **J** → **C**.
  *
  * Represents a cocone (*X*, *ψ*), where
  *   - *X* is the apex, an object of **C**
  *   - *ψ*_*A*: *D*[*A*] → *X* is the leg at an object *A* of **J**
  */
abstract class Cocone(tracked val D: Functor) extends caps.Pure {
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

  /** *ψ*_*A*: *D*[*A*] → *X*
    *
    * The legs form a natural transformation from *D* to the constant functor at *X*.
    */
  def leg[A: J.Obj]: F[A] ==> Apex

  /** The cocone (*Y*, *h* ∘ *ψ*) induced by a morphism *h*: *X* → *Y*. */
  final def induced[Y: C.Obj as obj](h: Apex ==> Y): Cocone { val D: Cocone.this.D.type; type Apex = Y } = {
    new Cocone(D) {
      type Apex = Y
      def apex: Y is C.Obj             = obj
      def leg[A: J.Obj]: F[A] ==> Apex = Cocone.this.leg[A] >>> h
    }
  }

  /** Laws that any `Cocone` must satisfy. */
  object CoconeLaws {

    /** *ψ*_*B* ∘ *D*(*f*) = *ψ*_*A*
      */
    def commutes[A: J.Obj, B: J.Obj](f: A --> B)(using (F[A] ==> Apex) is Observable): Boolean = {
      (map(f) >>> leg[B]) =?= leg[A]
    }
  }
}
