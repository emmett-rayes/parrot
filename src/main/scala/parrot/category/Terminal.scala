package parrot
package category

/** A terminal object of a category **C**.
  *
  * Represents a terminal object *I*, where
  *   - !: *A* → *I* is the unique morphism from an object *A*
  */
abstract class Terminal(tracked override val C: Category, tracked override val U: C.Obj) extends Category.Object(C, U) {
  import C.{Obj, -->}

  /** The terminal object *I*. */
  final type I = U.Self

  /** The unique morphism !: *A* → *I*. */
  def discard[A: Obj]: A --> I

  /** The terminal object as a limit of the empty diagram, with ! as the factorization. */
  final lazy val limit: Terminal.AsLimit { val T: Terminal.this.type } = Terminal.AsLimit(this)

  /** Laws that any `Terminal` must satisfy. */
  object TerminalLaws {

    /** *f* = ! for every *f*: *A* → *I*
      */
    def uniqueness[A: Obj](f: A --> I)(using (A --> I) is Observable): Boolean = {
      f =?= discard[A]
    }
  }
}

object Terminal {
  import Category.Empty

  /** The terminal objects of **K**. */
  type Of[K <: Category] = Terminal { val C: K }

  /** The terminal object of a category with limits of the empty shape: the limit of the empty diagram. */
  def apply(L: Limits { val J: Empty.type }): Of[L.C.type] = {
    FromLimit(L.limit(EmptyDiagram(L.C)))
  }

  /** The terminal object of a limit *L* of the empty diagram.
    *
    * The terminal object is the apex of *L*, and ! is the factorization through *L* of the cone with apex *A*, which
    * has no legs.
    */
  open class FromLimit(tracked val L: Limit.Of[EmptyDiagram]) extends Terminal(L.D.K, L.X) {
    import C.{Obj, -->}

    def discard[A: Obj as obj]: A --> I = {
      L.factor(EmptyCone(L.D, obj))
    }
  }

  /** A terminal object *T* as a limit of the empty diagram.
    *
    * The apex of the limit is *I*, its cones have no legs, and the factorization of the cone with apex *A* is !: *A* →
    * *I*.
    */
  final class AsLimit(tracked val T: Terminal) extends Limit(EmptyDiagram(T.C), T.U) {
    import T.C.-->

    def leg[A: Empty.Absurd]: T.I --> Nothing = {
      A.absurd
    }

    def factor(K: Cone.Of[D.type]): K.Apex --> T.I = {
      T.discard[K.Apex](using K.X)
    }
  }

  /** The cone with apex *X* over a diagram of the empty shape.
    *
    * The empty cone has no legs.
    */
  final class EmptyCone(tracked override val D: Functor { val C: Empty.type }, tracked override val X: D.D.Obj)
      extends Cone(D, X) {
    import D.D.-->

    def leg[A: Empty.Absurd]: Apex --> D.F[A] = {
      A.absurd
    }
  }

  /** The empty diagram **0** → **K**, the unique functor out of the empty category.
    */
  final class EmptyDiagram(tracked val K: Category) extends Functor(Empty, K) {
    import K.--> as ==>
    import Empty.{Absurd, -->}

    type Self[A] = Nothing

    def objects[A: Absurd]: Nothing is K.Obj = {
      A.absurd
    }

    def map[A: Absurd, B: Absurd](f: A --> B): Nothing ==> Nothing = {
      A.absurd
    }
  }
}
