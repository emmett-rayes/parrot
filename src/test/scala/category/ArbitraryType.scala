package parrot
package category

import org.scalacheck.{Arbitrary, Cogen, Gen}

import scala.compiletime.deferred

trait ArbitraryType {
  type T
  given arb: Arbitrary[T]        = deferred
  given cogen: Cogen[T]          = deferred
  given eq: (T is Eq)            = deferred
  given canEqual: CanEqual[T, T] = deferred
}

object ArbitraryType {
  def ofSize(n: Int): ArbitraryType = new ArbitraryType {
    type T = Int
    override given arb: Arbitrary[T]        = Arbitrary(Gen.choose(0, n - 1))
    override given cogen: Cogen[T]          = Cogen[Int]
    override given eq: (T is Eq)            = summon[Int is Eq]
    override given canEqual: CanEqual[T, T] = CanEqual.derived
  }

  given Arbitrary[ArbitraryType] = Arbitrary(
    Gen.oneOf(1, 2, 3, 8, 100, 10000).map(ofSize)
  )
}
