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
      "-language:experimental.saferExceptions",
      "-language:strictEquality",
      "-preview",
      "-source:future",
      "-unchecked",
    ),
    libraryDependencies ++= Seq(
      "org.scalatest"     %% "scalatest"       % "3.2.20"   % Test,
      "org.scalatestplus" %% "scalacheck-1-19" % "3.2.20.0" % Test,
    ),
  )
