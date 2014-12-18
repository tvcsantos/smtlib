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
import java.io.IOException

class Z3SolverWeb(fsimpl:Simplifier[Formula],
    ffn:FreeNamesVisitor[Formula],
    ffv:FreeVariablesVisitor[Formula, Identifier],
    ftc:TypeChecker[Formula, Type, Unit],
    fsubst:SubstitutionVisitor[Formula, Term]) 
    extends Z3SolverProcess(fsimpl, ffn, ffv, ftc, fsubst, null) {
  
  override protected[smt] def newInstance():scala.smt.SMTSolver =
    new Z3SolverWeb(fsimpl, ffn, ffv, ftc, fsubst)
  
  import scala.smt._
  
  import SMTResult._  
  
  override protected def runSolver(code:String):Stream[String] = {
    import scalaj.http.HttpRequest
    import scalaj.http.Http
    import scalax.util.ScalaException
    try {
    val request: HttpRequest =
      Http("http://rise4fun.com/rest/ask/z3/").postData(code)

    val response = request.asString
    Stream(response.body.split("\n"):_*)
    } catch {
      case x:IOException => throw 
    		  ScalaException[SMTSolverProcessException](x, code) 
    }
  }

}