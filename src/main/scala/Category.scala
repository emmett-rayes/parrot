package parrot

/** A category encoded in **Type**.
  *
  * Represents a category with objects from **Type** and hom-sets given by *~>*, where
  *   - *~>*: **Type**^*op* × **Type** → **Type** is the hom-profunctor
  *   - *id*: *A* ~> *A* is the identity morphism
  *   - ∘: (*B* ~> *C*) × (*A* ~> *B*) → (*A* ~> *C*) is composition of morphisms
  */
trait Category {
  type Self[_, _]
  type ~> = Self

  /** The identity morphism *id*: *A* ~> *A*.
    *
    * Unitality:
    *   - left identity: *id* ∘ *f* = *f*
    *     - `id.compose(f) == f`
    *   - right identity: *f* ∘ *id* = *f*
    *     - `f.compose(id) == f`
    */
  def id[A]: A ~> A

  extension [B, C](self: B ~> C)
    /** Composes a morphism *g*: *B* ~> *C* with a morphism *f*: *A* ~> *B* to a morphism *g* ∘ *f*: *A* ~> *C*.
      *
      * Associativity:
      *   - (*f* ∘ *g*) ∘ *h* = *f* ∘ (*g* ∘ *h*)
      *     - `self.compose(other1).compose(other2) == self.compose(other1.compose(other2))`
      */
    def compose[A](other: A ~> B): A ~> C

  extension [A, B](self: A ~> B)
    /** Composes a morphism *f*: *A* ~> *B* with a morphism *g*: *B* ~> *C* to a morphism *f* ; *g*: *A* ~> *C* in
      * so-called diagrammatic order.
      */
    def andThen[C](other: B ~> C): A ~> C = {
      other.compose(self)
    }
}

object Category {

  /** Summons the `Category` instance of `~>`. */
  def apply[~>[_, _]: Category]: ~> is Category = {
    summon
  }
}
