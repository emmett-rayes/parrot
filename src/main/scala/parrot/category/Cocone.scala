package parrot
package category

/** A cocone under a diagram *D*: **J** → **C**.
  *
  * Represents a cocone (*X*, *ψ*), where
  *   - *X* is the apex, an object of **C**
  *   - *ψ*_*A*: *D*[*A*] → *X* is the leg at an object *A* of **J**
  */
abstract class Cocone(tracked val D: Functor, tracked val X: D.D.Obj) extends caps.Pure {
  import D.{F as D, map}
  import D.C as J
  import D.D as C
  import J.-->
  import C.--> as ==>

  /** The apex *X*. */
  final type Apex = X.Self

  private given ApexIsObj: Apex is C.Obj              = X
  private given DIsObj: [A: J.Obj] => (D[A] is C.Obj) = D.objects[A]

  /** *ψ*_*A*: *D*[*A*] → *X*
    *
    * The legs form a natural transformation from *D* to the constant functor at *X*.
    */
  def leg[A: J.Obj]: D[A] ==> Apex

  /** The cocone (*Y*, *h* ∘ *ψ*) induced by a morphism *h*: *X* → *Y*. */
  final def induced[Y: C.Obj as obj](h: Apex ==> Y): Cocone.Of[D.type] { val X: obj.type } = {
    new Cocone(D, obj) {
      def leg[A: J.Obj]: D[A] ==> Y = {
        Cocone.this.leg[A] >>> h
      }
    }
  }

  /** Laws that any `Cocone` must satisfy. */
  object CoconeLaws {

    /** *ψ*_*B* ∘ *D*(*f*) = *ψ*_*A*
      */
    def commutes[A: J.Obj, B: J.Obj](f: A --> B)(using (D[A] ==> Apex) is Observable): Boolean = {
      (map(f) >>> leg[B]) =?= leg[A]
    }
  }
}

object Cocone {

  /** Refines `Cocone` to a specific functor **F**. */
  type Of[F <: Functor] = Cocone { val D: F }
}
