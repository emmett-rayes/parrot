# --- Main ---

scala_sources(
    name="main",
    sources=["src/main/scala/**/*.scala"],
)


# --- Tests ---

scalatest_tests(
    name="tests",
    sources=["src/test/scala/**/*Test.scala"],
)

scala_sources(
    name="test-utils",
    sources=["src/test/scala/**/*.scala", "!src/test/scala/**/*Test.scala"],
    dependencies=[":json-fixtures"],
)

files(
    name="json-fixtures",
    sources=["src/test/resources/json/**/*"],
)


# --- Third-party (run `pants generate-lockfiles` after editing) ---

jvm_artifact(
    name="scala3-library",
    group="org.scala-lang",
    artifact="scala3-library_3",
    version="3.9.0",
)

scala_artifact(
    name="scalatest",
    group="org.scalatest",
    artifact="scalatest",
    version="3.2.20",
    packages=["org.scalatest.**"],
)

scala_artifact(
    name="scalacheck",
    group="org.scalatestplus",
    artifact="scalacheck-1-19",
    version="3.2.20.0",
    packages=["org.scalatestplus.scalacheck.**"],
)
