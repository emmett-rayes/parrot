package parrot
package category

/** An initial object of a category **C**.
  *
  * Represents an initial object *I*, where
  *   - ¡: *I* → *A* is the unique morphism to an object *A*
  */
abstract class Initial(tracked override val C: Category, tracked override val U: C.Obj) extends Category.Object(C, U) {
  import C.{Obj, -->}

  /** The initial object *I*. */
  final type I = U.Self

  /** The unique morphism ¡: *I* → *A*. */
  def absurd[A: Obj]: I --> A

  /** The initial object as a colimit of the empty diagram, with ¡ as the factorization. */
  final lazy val colimit: Initial.AsColimit { val I: Initial.this.type } = Initial.AsColimit(this)

  /** Laws that any `Initial` must satisfy. */
  object InitialLaws {

    /** *f* = ¡ for every *f*: *I* → *A*
      */
    def uniqueness[A: Obj](f: I --> A)(using (I --> A) is Observable): Boolean = {
      f =?= absurd[A]
    }
  }
}

object Initial {
  import Category.Empty
  import Terminal.EmptyDiagram

  /** The initial objects of **K**. */
  type Of[K <: Category] = Initial { val C: K }

  /** The initial object of a category with colimits of the empty shape: the colimit of the empty diagram. */
  def apply(L: Colimits { val J: Empty.type }): Of[L.C.type] = {
    FromColimit(L.colimit(EmptyDiagram(L.C)))
  }

  /** The initial object of a colimit *L* of the empty diagram.
    *
    * The initial object is the apex of *L*, and ¡ is the factorization through *L* of the cocone with apex *A*, which
    * has no legs.
    */
  open class FromColimit(tracked val L: Colimit.Of[EmptyDiagram]) extends Initial(L.D.K, L.X.U) {
    import C.{Obj, -->}

    def absurd[A: Obj]: I --> A = {
      L.factor(EmptyCocone(L.D, C.Object[A]))
    }
  }

  /** An initial object *I* as a colimit of the empty diagram.
    *
    * The apex of the colimit is *I*, its cocones have no legs, and the factorization of the cocone with apex *A* is ¡:
    * *I* → *A*.
    */
  final class AsColimit(tracked val I: Initial) extends Colimit(EmptyDiagram(I.C), I) {
    import I.C.-->

    def leg[A: Empty.Absurd]: Nothing --> I.I = {
      A.absurd
    }

    def factor(K: Cocone.Of[D.type]): I.I --> K.Apex = {
      I.absurd[K.Apex](using K.X.U)
    }
  }

  /** The cocone with apex *X* under a diagram of the empty shape.
    *
    * The empty cocone has no legs.
    */
  final class EmptyCocone(tracked override val D: Functor { val C: Empty.type }, tracked override val X: D.D.Object)
      extends Cocone(D, X) {
    import D.D.-->

    def leg[A: Empty.Absurd]: D.F[A] --> Apex = {
      A.absurd
    }
  }
}
