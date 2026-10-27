package parrot
package category

import org.scalacheck.util.Pretty
import org.scalacheck.{Gen, Prop, Test}
import org.scalatest.BeforeAndAfterAll
import org.scalatest.funsuite.AnyFunSuite

import java.nio.charset.StandardCharsets.UTF_8
import java.nio.file.{Files, Path, Paths, StandardCopyOption}
import scala.collection.mutable.ListBuffer
import scala.jdk.CollectionConverters.*

/** Base class of law tests: every law check is a test, and its outcome is recorded in the law status table.
  *
  * A law check generates its arguments and its observations (with fresh sample points) and evaluates the law, which
  * returns a `Boolean`. A counterexample search generates arguments until the law fails.
  */
abstract class LawSuite(structure: String, instance: String) extends AnyFunSuite, BeforeAndAfterAll {

  /** The number of generated cases per law. */
  protected val cases: Int = 200

  private val rows = ListBuffer.empty[LawStatus.Row]

  /** What the laws of this suite are about: `instance`, as an instance of `structure`. */
  protected given subject: LawSuite.Subject = LawSuite.Subject(structure, instance)

  /** Registers `checks` for the laws of another structure that the instance has as well, such as the functor of a
    * monad: inside, [[law]] and [[counterexample]] are about the instance as an instance of `structure`.
    */
  protected def also(structure: String)(checks: LawSuite.Subject ?=> Unit): Unit = {
    checks(using LawSuite.Subject(structure, subject.instance))
  }

  /** Registers the check of a law of `subject`. */
  protected def law(name: String, note: String = "")(using subject: LawSuite.Subject)(check: => Prop): Unit = {
    test(s"${subject.instance} is ${subject.structure}: $name") {
      val result = Test.check(Test.Parameters.default.withMinSuccessfulTests(cases), check)
      val status = if result.passed then "Tested" else "Fails"
      record(LawStatus.Row(subject.structure, name, subject.instance, status, note))
      if !result.passed then fail(Pretty.pretty(result, Pretty.Params(2)))
    }
  }

  /** Registers a counterexample: a law that does not hold for `subject`, with a witness found by `search`. */
  protected def counterexample(name: String, note: String = "")(using subject: LawSuite.Subject)(
    search: => Prop
  ): Unit = {
    test(s"${subject.instance} is not ${subject.structure}: $name fails") {
      val result = Test.check(Test.Parameters.default.withMinSuccessfulTests(cases), search)
      val found  = !result.passed
      val status = if found then "Fails (counterexample)" else "Not refuted"
      record(LawStatus.Row(subject.structure, name, subject.instance, status, note))
      assert(found, s"no counterexample to $name found")
    }
  }

  /** The law holds for all generated arguments. */
  protected def forAll[A](a: Gen[A])(law: A => Boolean): Prop = {
    Prop.forAllNoShrink(a)(law)
  }

  /** The law holds for all generated arguments. */
  protected def forAll[A, B](a: Gen[A], b: Gen[B])(law: (A, B) => Boolean): Prop = {
    Prop.forAllNoShrink(a, b)(law)
  }

  /** The law holds for all generated arguments. */
  protected def forAll[A, B, C](a: Gen[A], b: Gen[B], c: Gen[C])(law: (A, B, C) => Boolean): Prop = {
    Prop.forAllNoShrink(a, b, c)(law)
  }

  /** The law holds for all generated arguments. */
  protected def forAll[A, B, C, D](a: Gen[A], b: Gen[B], c: Gen[C], d: Gen[D])(law: (A, B, C, D) => Boolean): Prop = {
    Prop.forAllNoShrink(a, b, c, d)(law)
  }

  /** The law holds for all generated arguments. */
  protected def forAll[A, B, C, D, E](a: Gen[A], b: Gen[B], c: Gen[C], d: Gen[D], e: Gen[E])(
    law: (A, B, C, D, E) => Boolean
  ): Prop = {
    Prop.forAllNoShrink(a, b, c, d, e)(law)
  }

  private def record(row: LawStatus.Row): Unit = {
    rows.synchronized {
      val _ = rows += row
    }
  }

  override def afterAll(): Unit = {
    try LawStatus.write(getClass.getName, rows.synchronized(rows.toList))
    finally super.afterAll()
  }
}

object LawSuite {

  /** What a law is about: `instance`, as an instance of `structure`. */
  final case class Subject(structure: String, instance: String)
}

/** The law status table: which law holds for which instance, and how we know. Regenerated after every test run. */
object LawStatus {

  /** One law of one structure, checked for one instance. */
  final case class Row(structure: String, law: String, instance: String, status: String, note: String)

  private val directory = Paths.get("target", "law-status")
  private val table     = Paths.get("docs", "law-status.md")

  /** Writes the rows of one suite, then regenerates the table from the rows of all suites. */
  def write(suite: String, rows: List[Row]): Unit = synchronized {
    val _     = Files.createDirectories(directory)
    val lines = rows.map(r => List(r.structure, r.law, r.instance, r.status, r.note).mkString("\t"))
    replace(directory.resolve(s"$suite.tsv"), lines.mkString("\n"))
    if Files.isDirectory(table.getParent) then replace(table, render(readAll()))
  }

  /** Whether the suite that wrote `file` still exists: rows of renamed or deleted suites are dropped. */
  private def current(file: Path): Boolean = {
    val suite = file.getFileName.nn.toString.stripSuffix(".tsv")
    scala.util.Try(Class.forName(suite)).isSuccess
  }

  private def readAll(): List[Row] = {
    val files = Files.list(directory).iterator().asScala.filter(_.toString.endsWith(".tsv")).filter(current).toList
    files.flatMap { file =>
      Files.readAllLines(file, UTF_8).asScala.toList.filter(_.nonEmpty).map { line =>
        line.split("\t", -1).toList match {
          case List(s, l, i, st, n) => Row(s, l, i, st, n)
          case other                => Row(other.mkString(" "), "", "", "malformed", "")
        }
      }
    }
  }

  private def render(rows: List[Row]): String = {
    val header = List(
      "# Law status",
      "",
      "Generated by the law tests (`src/test/scala/category/LawSuite.scala`) after each test run; do not edit.",
      "",
      "| Status | Meaning |",
      "| --- | --- |",
      "| Tested | the law held on every generated case |",
      "| Fails (counterexample) | the law does not hold for this instance; a test exhibits a counterexample |",
      "| Fails | the law failed in the last run: a bug |",
      "",
    )
    val sections = rows.groupBy(_.structure).toList.sortBy(_._1).flatMap { (structure, rs) =>
      List(s"## $structure", "", "| Law | Instance | Status | Note |", "| --- | --- | --- | --- |") ++
        rs.distinct.sortBy(r => (r.law, r.instance)).map(r =>
          s"| ${r.law} | ${r.instance} | ${r.status} | ${r.note} |"
        ) ++
        List("")
    }
    (header ++ sections).mkString("\n")
  }

  private def replace(path: Path, content: String): Unit = {
    val temporary = Files.createTempFile(directory, "law-status", ".tmp")
    val _         = Files.write(temporary, content.getBytes(UTF_8))
    val _         = Files.move(temporary, path, StandardCopyOption.REPLACE_EXISTING, StandardCopyOption.ATOMIC_MOVE)
  }
}
