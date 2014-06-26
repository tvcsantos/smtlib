package scala.smt.z3

import scala.smt.visitor.Simplifier
import scala.smt.visitor.SubstitutionVisitor
import scala.smt.visitor.FreeVariablesVisitor
import scala.smt.visitor.TypeChecker
import scala.smt.Formula

class Z3SolverAPIParse(fsimpl:Simplifier[Formula], 
    ffv:FreeVariablesVisitor[Formula],
    ftc:TypeChecker[Formula],
    fsubst:SubstitutionVisitor[Formula]) 
    extends Z3SolverProcess(fsimpl, ffv, ftc, fsubst) {
  
  override protected[smt] def newInstance():scala.smt.SMTSolver =
    new Z3SolverAPIParse(fsimpl, ffv, ftc, fsubst)
  
  import z3.scala.{Z3Config, Z3Context}
  
  import scala.smt._
  
  import SMTResult._  
  
  val cfg = new Z3Config("MODEL" -> false)

  override def runSMT(code:String):Option[SMTResult] = {  
    val z3ctx = new Z3Context(cfg)
    z3ctx.config.setParamValue("MODEL", getModel.toString)
    val parsedAST = z3ctx.parseSMTLIB2String(code)
    z3ctx.assertCnstr(parsedAST)
    val r = z3ctx.check
    z3ctx.delete
    r match {
      case None => None
      case Some(true) => Some(SMTResult.SAT)
      case Some(false) => Some(SMTResult.UNSAT)
    }
  }

}