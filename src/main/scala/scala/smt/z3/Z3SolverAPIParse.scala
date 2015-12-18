package scala.smt.z3

import scalax.visitor.SubstitutionVisitor
import scalax.visitor.FreeNamesVisitor
import scalax.visitor.FreeVariablesVisitor
import scalax.visitor.TypeChecker
import scalax.visitor.Simplifier
import scala.smt.Formula
import scala.smt.Term
import scala.smt.Type
import scala.smt.Identifier

class Z3SolverAPIParse(fsimpl:Simplifier[Formula],
    ffn:FreeNamesVisitor[Formula],
    ffv:FreeVariablesVisitor[Formula, Identifier],
    ftc:TypeChecker[Formula, Type, Unit],
    fsubst:SubstitutionVisitor[Formula, Term], bin:String) 
    extends Z3SolverProcess(fsimpl, ffn, ffv, ftc, fsubst, bin) {
  
  override protected[smt] def newInstance():scala.smt.SMTSolver =
    new Z3SolverAPIParse(fsimpl, ffn, ffv, ftc, fsubst, bin)
  
  import z3.scala.{Z3Config, Z3Context}
  
  import scala.smt._
  
  import SMTResult._  
  
  val cfg = new Z3Config("MODEL" -> false)

  override def runSMT(code:String):Option[SMTResult] = {
    val z3ctx = new Z3Context(cfg)
    z3ctx.config.setParamValue("MODEL", getModel.toString)
    val parsedAST = z3ctx.parseSMTLIB2String(code)
    val z3solver = z3ctx.mkSolver()
    z3solver/*z3ctx*/.assertCnstr(parsedAST)
    val r = z3solver/*z3ctx*/.check
    z3ctx.delete
    r match {
      case None => None
      case Some(true) => Some(SMTResult.SAT)
      case Some(false) => Some(SMTResult.UNSAT)
    }
  }

}