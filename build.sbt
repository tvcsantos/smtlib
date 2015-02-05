import AssemblyKeys._

assemblySettings

name := "smtlib"

version := "1.0"

scalaVersion := "2.10.4"

libraryDependencies += "org.scala-lang" % "scala-reflect" % scalaVersion.value

jarName in assembly := "smtlib.jar"