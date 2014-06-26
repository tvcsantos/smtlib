package scala.smt.test

import scala.smt.QuantifiedFormula

object Z3TestSMTLIB {
  
  import scala.smt.SMTSolver  
  import scala.smt.Formula
  import scala.smt.Predicate
  import scala.smt.QuantifiedFormula
  import scala.smt.Quantifier
  import scala.smt.Quantifier._
  import scala.smt.IntType
  import scala.smt.Imp
  import scala.smt.Variable
  import scala.smt.NumLit
  import scala.smt.Function
  
  import scala.smt.z3.Z3SolverAPI
    import scala.smt.cvc4.CVC4SolverProcess
    import scala.smt.z3.Z3SolverProcess
    import scala.smt.z3.Z3SolverAPIParse
    
    import scala.smt.visitor.{
      TermFreeNames => SMTTermFreeNames,
      FormulaFreeNames => SMTFormulaFreeNames,
      TermSimplifier => SMTTermSimplifier,
      FormulaSimplifier => SMTFormulaSimplifier,
      TermSubstitution => SMTTermSubstitution,
      FormulaSubstitution => SMTFormulaSubstitution,
      TermFreeVariables => SMTTermFreeVariables,
      FormulaFreeVariables => SMTFormulaFreeVariables,
      TermTypeChecker => SMTTermTypeChecker,
      FormulaTypeChecker => SMTFormulaTypeChecker
    }
  
  def main(args: Array[String]):Unit = {  
    
    val tfn = new SMTTermFreeNames
    val ffn = new SMTFormulaFreeNames(tfn)
    val tsimpl = new SMTTermSimplifier
    val fsimpl = new SMTFormulaSimplifier(tsimpl, ffn)
    val tsubst = new SMTTermSubstitution
    val fsubst = new SMTFormulaSubstitution(tsubst, tfn)
    val tfv = new SMTTermFreeVariables
    val ffv = new SMTFormulaFreeVariables(tfv)
    val ttc = new SMTTermTypeChecker
    val ftc = new SMTFormulaTypeChecker(ttc)
    
    val solver:SMTSolver = new Z3SolverAPI(fsimpl, ffv, ftc, fsubst)
    
    //solver.setModel(true)
    
    /*val f = QuantifiedFormula(EXISTENTIAL, List(("x", IntType)),
        Imp(Predicate(">", List(Variable("x", Some(IntType)), NumLit(0))),
            QuantifiedFormula(EXISTENTIAL, List(("y", IntType)),
                Predicate(">", List(
                    Function("+", 
                        List(Variable("x", Some(IntType)), 
                            Variable("y", Some(IntType))), Some(IntType)),
                    NumLit(0)))
            )
        )
    )*/
    
    import scala.smt.Equality
    
    def getVar(name:String) = Variable(name, Some(IntType))
    
    val xv = getVar("x")
    //val vv = getVar("v")
    
    def ff(fname:String, v:Variable) = Function(fname, List(v), Some(IntType))
   
    def qf(a:String, s:String) = QuantifiedFormula(EXISTENTIAL, 
        List(("v", IntType)),
        Equality(ff(a, getVar(s)), getVar("v")))
    
    /*val f = QuantifiedFormula(EXISTENTIAL, List(("v", IntType)),
        Equality(xv, vv))*/
            
            //solver.setModel(true)
            
    solver.assert(Equality(xv, 
        Function("+", List(NumLit(2), NumLit(1)), Some(IntType))))
        
    solver.assert(Equality(getVar("y"), 
        Function("+", List(NumLit(2), NumLit(2)), Some(IntType))))
    
    solver.assert(qf("a", "x"))
    
    solver.assert(qf("b", "x"))
    
    //solver.assert(coco("z"))
    
    //solver.assert(Equality(xv, NumLit(4)))
    
    //solver.setModel(false)
    
    solver.checkSatWithModel match {
      case None => println("unknown")
      case Some((x, m)) =>
        println(x)
      	m match {
          case None => println("no model")
          case Some(y) =>
            println(y.getValue("x").get)
            println(y.getValue("y").get)
        }
    }
    
    //println(solver.checkSatWithModel())
    
  }
}