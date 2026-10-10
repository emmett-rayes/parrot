scalaVersion := "3.9.0"

lazy val root = rootProject
  .settings(
    name             := "Parrot",
    idePackagePrefix := Some("parrot"),
    scalacOptions ++= Seq(
      "-Wnonunit-statement",
      "-Wsafe-init",
      "-Wunused:all",
      "-Wvalue-discard",
      "-Yexplicit-nulls",
      "-deprecation",
      "-explain",
      "-explain-types",
      "-feature",
      "-language:experimental.genericNumberLiterals",
      "-language:experimental.modularity",
      "-language:experimental.pureFunctions",
      "-language:strictEquality",
      "-preview",
      "-source:future",
      "-unchecked",
    ),
    libraryDependencies ++= Seq(
      "org.scalatest"     %% "scalatest"       % "3.2.20"   % Test,
      "org.scalatestplus" %% "scalacheck-1-19" % "3.2.20.0" % Test,
    ),
    // exclude legacy
    ideExcludedDirectories := Seq(
      (Compile / scalaSource).value / "legacy",
      (Test / scalaSource).value / "legacy",
    ),
    Compile / unmanagedSources := (Compile / unmanagedSources).value.filterNot(_.getPath.contains("/legacy/")),
    Test / unmanagedSources    := (Test / unmanagedSources).value.filterNot(_.getPath.contains("/legacy/")),
    // benchmarks (Test/runMain) run in their own JVM, with a fixed heap that fits the parse trees of large documents
    Test / run / fork           := true,
    Test / run / javaOptions ++= Seq("-Xms6g", "-Xmx6g", "-Xss16m"),
    Test / run / outputStrategy := Some(StdoutOutput),
  )
