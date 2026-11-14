package parrot
package benchmarks

import json.{JsonBenchmark, JsonGrammar}
import parser.StrictParser

/** A library with its port of a grammar: how the harness runs it, and the tree it builds of a whole document, in a form
  * that compares with the trees of the other ports.
  */
final case class Library(interpreter: JsonBenchmark.Interpreter, tree: String => Option[Any]) {
  def name: String = interpreter.name
}

object Library {

  /** A library whose port parses a whole document into `parse`, and whose tree compares as `compared`. */
  def apply(name: String, parse: String => Option[Any], compared: Any => Any = identity): Library = {
    Library(JsonBenchmark.Interpreter(name, input => parse(input).isDefined), input => parse(input).map(compared))
  }
}

/** A JSON grammar and its ports. The first library is the reference: every port must accept what it accepts and build
  * its tree.
  */
final case class Grammar(name: String, libraries: List[Library]) {
  def reference: Library = libraries.head

  def library(name: String): Option[Library] = libraries.find(_.name.equalsIgnoreCase(name))
}

object Grammars {
  private val parser = StrictParser()

  /** Parrot's tree of a whole document with JsonGrammar. */
  private val jsonGrammar = JsonGrammar(parser)

  def parrotTree(input: String): Option[JsonGrammar.JsonJson] = {
    parser.parse(jsonGrammar.json)(input).toOption.filter(_.offset == input.length).map(_.result)
  }

  /** Parrot's JsonGrammar, run by Parrot as in JsonBenchmark, and its ports, whose trees compare in Parrot's types. */
  val parrot: Grammar = Grammar(
    "JsonGrammar",
    List(
      Library(JsonBenchmark.strict.copy(name = "Parrot"), parrotTree),
      Library("parboiled2", Parboiled2Json.parseDocument, Trees.toParrot),
      Library("fastparse", FastparseJson.parseDocument, Trees.toParrot),
      Library("cats-parse", CatsParseJson.parseDocument, Trees.toParrot),
      Library("Parsley", ParsleyJson.parseDocument, Trees.toParrot),
    ),
  )

  private val parrotJs = ParrotJs(parser)

  /** fastparse's documented JSON grammar, with fastparse as the reference, and its ports, which all build [[Js]]. */
  val fastparse: Grammar = Grammar(
    "fastparse",
    List(
      Library("fastparse", FastparseJs.parseDocument),
      Library("Parrot", input => parser.parse(parrotJs.jsonExpr)(input).toOption.filter(_.offset == input.length).map(_.result)),
      Library("parboiled2", Parboiled2Js.parseDocument),
      Library("cats-parse", CatsParseJs.parseDocument),
      Library("Parsley", ParsleyJs.parseDocument),
    ),
  )

  val all: List[Grammar] = List(parrot, fastparse)
}
