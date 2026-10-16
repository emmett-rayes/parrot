package parrot
package parser

import category.Cocartesian

/** Implements branching and merging from coproducts on `Self`. */
trait Branching extends ParserAlgebra {
  override type Self[_, _]: Cocartesian.`with`[None, Alternative] as BranchingCocartesian

  val SelfIsCocartesian: Self is Cocartesian.`with`[None, Alternative] = BranchingCocartesian
  import SelfIsCocartesian.{+++, left, right, |||}

  override def branch[A, B, C, D](self: P[A, B], other: P[C, D]): P[A + C, B + D] = {
    self +++ other
  }

  override def merge[A, B, C](self: P[A, B], other: P[C, B]): P[A + C, B] = {
    self ||| other
  }

  override def or[A, B, C](self: P[A, B], other: P[A, C]): P[A, B + C] = {
    (self >> left) |> (other >> right)
  }
}
