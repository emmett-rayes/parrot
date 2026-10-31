package parrot
package category

/** A base trait for type classes.
  *
  * Used to represent evidence that a type belongs to a certain type class. See [[Category]].
  */
trait Type extends caps.Pure {
  type Self
}

object Type {

  /** Summons the `Type` instance of `T`. */
  def apply[T: Type]: T is Type = summon

  /** Every type of kind `*` is trivially a `Type` without further structure. */
  given TIsType: [T] => T is Type {}
}
