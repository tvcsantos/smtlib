package scala.smt

object SMTExecutionMode extends Enumeration {
  type SMTExecutionMode = Value
  val AUTOMATIC, MIXED, INTERACTIVE = Value
}
  