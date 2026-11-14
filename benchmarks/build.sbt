// A build of its own, so that the libraries Parrot is compared with stay out of Parrot's build, which has no
// dependencies. It compiles Parrot and its JSON benchmark harness from their sources in the parent directory.

scalaVersion := "3.10.0"

/** The compiler options of Parrot, as in ../build.sbt. */
val parrotOptions = Seq(
  "-deprecation",
  "-explain-types",
  "-explain",
  "-feature",
  "-language:experimental.captureChecking",
  "-language:experimental.genericNumberLiterals",
  "-language:experimental.modularity",
  "-language:experimental.pureFunctions",
  "-language:experimental.saferExceptions",
  "-language:strictEquality",
  "-preview",
  "-source:future",
  "-unchecked",
  "-Wnonunit-statement",
  "-Wunused:privates,locals,params,patvars",
  "-Wvalue-discard",
  "-Yexplicit-nulls",
)

/** The repository of Parrot, the parent of this build. */
def repository(base: File): File = base.getParentFile.getParentFile

/** Parrot's main sources. */
lazy val parrot = project
  .in(file("parrot"))
  .settings(
    Compile / unmanagedSourceDirectories := Seq(repository(baseDirectory.value) / "src" / "main" / "scala"),
    scalacOptions ++= parrotOptions,
  )

/** The test sets and the harness of Parrot's JSON benchmark, from its tests. */
lazy val harness = project
  .in(file("harness"))
  .dependsOn(parrot)
  .settings(
    Compile / unmanagedSourceDirectories := Seq(
      repository(baseDirectory.value) / "src" / "test" / "scala" / "parrot" / "json"
    ),
    Compile / unmanagedSources / includeFilter := "JsonFixtures.scala" || "JsonBenchmark.scala",
    scalacOptions ++= parrotOptions,
  )

/** The ports of JsonGrammar to the other libraries, and the programs that check and measure them. */
lazy val root = rootProject
  .dependsOn(harness)
  .settings(
    name := "parrot-benchmarks",
    libraryDependencies ++= Seq(
      "org.parboiled"     %% "parboiled"  % "2.5.1",
      "com.lihaoyi"       %% "fastparse"  % "3.1.1",
      "org.typelevel"     %% "cats-parse" % "1.1.0",
      "com.github.j-mie6" %% "parsley"    % "4.6.2",
    ),
    scalacOptions ++= Seq(
      "-deprecation",
      "-feature",
      "-language:experimental.modularity",
      // fastparse's macros inline Predef.ArrowAssoc, deprecated since Scala 3.10, into the parsers.
      "-Wconf:msg=ArrowAssoc:s",
    ),
    fork        := true,
    javaOptions += "-Xmx4g",
    // The test sets are found from the root of the repository.
    Compile / run / baseDirectory := baseDirectory.value.getParentFile,
  )
