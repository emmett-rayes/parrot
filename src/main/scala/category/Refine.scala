package parrot
package category

/** Refines the underlying type `On` of `A` to `B`. */
infix type on[A <: Any { type On <: AnyKind }, B <: AnyKind] = A { type On = B }

/** Refines the unit object `I` of `A` to `B`. */
infix type withUnit[A <: Any { type I <: AnyKind }, B <: AnyKind] = A { type I = B }

/** Refines the `Tensor` product of `A` to `B`. */
infix type withTensor[A <: Any { type Tensor <: AnyKind }, B <: AnyKind] = A { type Tensor = B }
