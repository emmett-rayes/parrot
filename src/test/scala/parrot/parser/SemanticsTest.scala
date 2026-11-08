package parrot
package parser

import category.*
import org.scalacheck.Gen

/** The equation of a semantics, on random grammars, for an interpreter. */
abstract class SemanticsSpec(name: String, tracked val semantics: Semantics) extends LawSuite("Semantics", name) {
  import semantics.algebra
  import semantics.SemanticsLaws.*

  private given CanEqual[Any, Any] = CanEqual.derived

  law("runDefinition") {
    val parsers = Grammars.terms.map(Grammars.interpret(algebra))
    val inputs  = Grammars.inputs

    given (Option[(Int, Int)] is Observable) = {
      Observable.EqIsObservable(using Eq.OptionIsEq(using Eq.Tuple2IsEq(using Eq.IntIsEq, Eq.IntIsEq)))
    }
    forAll(parsers, Gen.choose(-5, 5), inputs) { (p, n, in) =>
      runDefinition(p)(n, in.source, in.offset)
    }
  }

  test(s"$name: parsers that agree at the start of every source can differ at other positions") {
    import algebra.*
    val anchored = regex("^b".r).rule("b")
    val plain    = literal("b").rule("b")
    val _        = assert(semantics.diagnose(anchored)((), "b") == semantics.diagnose(plain)((), "b"))
    val _        = assert(semantics.diagnose(anchored)((), "ab") == semantics.diagnose(plain)((), "ab"))
    assert(semantics.diagnose(anchored)((), "ab", 1) != semantics.diagnose(plain)((), "ab", 1))
  }
}

class ReferenceParserSemanticsTest extends SemanticsSpec("ReferenceParser", Interpreters.reference.Semantics)

class StrictParserSemanticsTest extends SemanticsSpec("StrictParser", Interpreters.strict.Semantics)
