package parrot
package category

/** Object evidence that every type has: the objects of a category whose objects are all closed types of kind \*.
  *
  * A category states which types are its objects with a type class selecting its objects (see [[Category]]). Refinements
  * of [[Type]], such as [[Eq]], select fewer objects and give programs information about each object.
  *
  * Type classes without parameters that are not categorical structures, such as this one, [[Eq]] and [[Observable]],
  * are traits; categorical structures take their bases as parameters and are abstract classes.
  *
  * @note Structure must be pure, so every type class of this library extends `caps.Pure`.
  */
trait Type extends caps.Pure {
  type Self
}

object Type {

  /** Summons the `Type` instance of `T`. */
  def apply[T: Type]: T is Type = summon

  /** Every type is a `Type`. */
  given TIsType: [T] => T is Type {}
}
