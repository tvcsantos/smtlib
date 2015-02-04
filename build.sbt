import AssemblyKeys._
import sbtrelease._
import ReleaseStateTransformations._
import ReleaseKeys._

assemblySettings

releaseSettings

name := "smtlib"

version := "1.0"

scalaVersion := "2.10.4"

libraryDependencies += "org.scala-lang" % "scala-reflect" % scalaVersion.value

jarName in assembly := "smtlib.jar"

releaseProcess := Seq[ReleaseStep](
  //checkOrganization,                // Look Ma', my own release step!
  checkSnapshotDependencies,
  inquireVersions,
  runTest,
  setReleaseVersion,
  //publishArtifacts,
  setNextVersion
)