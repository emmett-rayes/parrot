scalaVersion := "3.9.0"

lazy val root = rootProject
  .settings(
    name             := "Parrot",
    idePackagePrefix := Some("parrot"),
    scalacOptions ++= Seq(
      "-Wnonunit-statement",
      // "-Wsafe-init", // false positives on tracked parameters forwarded to a parent class (docs/DESIGN.md §10)
      "-Wunused:all",
      "-Wvalue-discard",
      "-Yexplicit-nulls",
      "-deprecation",
      "-explain",
      "-explain-types",
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
    ),
    // Tests run in their own JVM: the reference interpreter needs more than sbt's heap on the deepest JSON documents.
    Test / fork := true,
    Test / javaOptions += "-Xmx4g",
    libraryDependencies ++= Seq(
      "org.scalatest"     %% "scalatest"       % "3.2.20"   % Test,
      "org.scalatestplus" %% "scalacheck-1-19" % "3.2.20.0" % Test,
    ),
  )
