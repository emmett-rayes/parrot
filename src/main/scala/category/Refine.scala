package parrot
package category

/** Refines the underlying type `On` of `A` to `B`. */
infix type on[A <: Any { type On <: AnyKind }, B <: AnyKind] = A { type On = B }
