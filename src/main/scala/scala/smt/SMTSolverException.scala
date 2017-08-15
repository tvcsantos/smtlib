package scala.smt

class SMTSolverException(msg: String) extends Exception(msg) {
  def this() {
    this(null)
  }
}

class SMTSolverProcessException(code: String, msg: String) 
	extends SMTSolverException(msg) {
  def this(code: String) {
    this(code, null)
  }
}