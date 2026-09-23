package parrot
package legacy

/** An endoprofunctor over **Type**.
  *
  * Represents a functor *P*: **Type**^*op* × **Type** → **Type**, where
  *   - *P*[*A*,*B*] is the object part, contravariant in *A* and covariant in *B*
  *   - *P*(*f*,*g*) is the morphism part
  */
trait Profunctor {
  type Self[_, _]
  type P = Self

  extension [A, B](self: P[A, B])
    /** Maps a pair of morphisms *f*: *C* → *A*, *g*: *B* → *D* to a morphism *P*[*A*,*B*] → *P*[*C*,*D*].
      *
      * Functoriality:
      *   - identity: *P*(*id*,*id*) = *id*
      *     - `self.dimap(identity, identity) == self`
      *   - composition: *P*(*f*,*g*) ∘ *P*(*f*',*g*') = *P*(*f*' ∘ *f*,*g* ∘ *g*')
      *     - `self.dimap(f, g).dimap(f2, g2) == self.dimap(f2 andThen f, g andThen g2)`
      */
    def dimap[C, D](f: C => A, g: B => D): P[C, D]

  extension [A, B](self: P[A, B])
    /** Maps a morphism *f*: *C* → *A* to a morphism *P*[*A*,*B*] → *P*[*C*,*B*]. */
    def lmap[C](f: C => A): P[C, B] = {
      self.dimap(f, identity[B])
    }

  extension [A, B](self: P[A, B])
    /** Maps a morphism *g*: *B* → *D* to a morphism *P*[*A*,*B*] → *P*[*A*,*D*]. */
    def rmap[D](g: B => D): P[A, D] = {
      self.dimap(identity[A], g)
    }
}

object Profunctor {

  /** Summons the `Profunctor` instance of `P`. */
  def apply[P[_, _]: Profunctor]: P is Profunctor = {
    summon
  }
}
