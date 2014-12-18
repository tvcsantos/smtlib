package scala.smt.z3

import scala.smt.Formula
import scala.smt.Term
import scala.smt.Identifier
import scala.smt.Type
import scalax.visitor.Simplifier
import scalax.visitor.SubstitutionVisitor
import scalax.visitor.FreeNamesVisitor
import scalax.visitor.FreeVariablesVisitor
import scalax.visitor.TypeChecker

class Z3SplitSolverAPI(
    fsimpl:Simplifier[Formula],
    ffn:FreeNamesVisitor[Formula],
    ffv:FreeVariablesVisitor[Formula, Identifier],
    ftc:TypeChecker[Formula, Type, Unit],
    fsubst:SubstitutionVisitor[Formula, Term]) 
    extends Z3SolverAPI(fsimpl, ffn, ffv, ftc, fsubst) {
  
  override protected[smt] def newInstance():scala.smt.SMTSolver =
    new Z3SplitSolverAPI(fsimpl, ffn, ffv, ftc, fsubst)
  
  import scala.smt._
  import SMTResult._
  
  override protected def checkSatImplAuto(as:Set[(Formula, AST)], 
      tm:Map[Type, TypeDef], 
      dm:Map[Type, (Sort, Set[FunDef], Set[TheoDef])]):Option[SMTResult] = {
    
    dm.foreach(d => d._2._3.foreach(z3ctx.assertCnstr(_)))
    
    val splitted = split(as)
        
    val rs = splitted.map(e => {
      z3ctx.push()
      e.foreach(x => z3ctx.assertCnstr(x._2))	
      val r = z3ctx.check match {
      	case None => None
      	case Some(true) => Some(SMTResult.SAT)
      	case Some(false) => Some(SMTResult.UNSAT)
      }
      if (z3ctx.getNumScopes > 0) z3ctx.pop(1)
      r
    })
    
    if (rs isEmpty) None
    else if (rs contains(None)) None
    else if (rs contains(Some(SMTResult.UNSAT)))
      Some(SMTResult.UNSAT)
    else Some(SMTResult.SAT)
    
  }
  
  protected def split(as:Set[(Formula, AST)]):Set[Set[(Formula, AST)]] = {
    var res:Set[Set[(Formula, AST)]] = Set()
    for (a <- as) {
      var resa = Set(a)
      
      var dep = a._1.visit(getFormulaFreeVariablesVisitor(), ())
      
      //first pass to get all the dependencies
      var changed = true
      while (changed) {
        changed = false
        for (b <- as) {
          val bfn = b._1.visit(getFormulaFreeVariablesVisitor(), ())
          if (!((dep & bfn) isEmpty)) {
            if (!((bfn -- dep) isEmpty))
            	changed = true
            dep ++= bfn
          }
        }
      }
      
      //second pass to get the assertions
      //based on the dependencies found
      for (b <- as) {
        val bfn = b._1.visit(getFormulaFreeVariablesVisitor(), ())
        if (!((dep & bfn) isEmpty))
          resa += b
      }
      
      res += resa
    }
    res
  }

  //def getFormulaFreeNamesVisitor():FreeNamesVisitor[Formula] = ffn
}