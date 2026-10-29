package parrot
package category

/** Object evidence that every type has: the objects of a category whose objects are all closed types of kind *.
  *
  * A category states which types its objects are with a type class selecting its objects (see [[Category]]).
  * Refinements of [[Type]], such as [[Eq]], select fewer objects and give programs information about each object.
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
