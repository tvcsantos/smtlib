package scala.smt

object SMTResult extends Enumeration {
  type SMTResult = Value
  val SAT, UNSAT = Value
}
