package parrot
package category

/** Refines the underlying type `Over` of *B* to *A*. */
infix type over[B <: Any { type Over <: AnyKind }, A <: AnyKind] = B { type Over = A }
