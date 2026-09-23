scalaVersion := "3.8.4"

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
      "-language:experimental.relaxedLambdaSyntax",
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
  )
