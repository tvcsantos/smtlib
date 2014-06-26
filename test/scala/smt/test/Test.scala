package scala.smt.test

import scala.smt.z3.Z3SolverAPI
    import scala.smt.cvc4.CVC4SolverProcess
    import scala.smt.z3.Z3SolverProcess
    import scala.smt.z3.Z3SolverAPIParse
   
    import scala.smt.{
      Formula => SMTFormula,
      Term => SMTTerm,
      SMTSolver,
      Type => SMTType,
      IntType => SMTIntType,
      BoolType => SMTBoolType,
      DataType => SMTDataType,
      FunType => SMTFunType,
      Equality => SMTEquality,
      Function => SMTFunction,
      Predicate => SMTPredicate,
      Variable => SMTVariable,
      NumLit => SMTNumLit,
      BoolLit => SMTBoolLit,
      Value => SMTValue,
      Equiv => SMTEquiv,
      QuantifiedFormula,
      Quantifier
    }

	import scala.smt.Quantifier._
    
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

object Test {

  def main(args: Array[String]): Unit = {
    
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
    
    /*val dt = DataType("Record", Seq(("mk-record", Seq(("m", IntType)))))
    
    val x = Variable("x", Some(dt))
    
    solver.assert(Predicate("=", 
        List(x, Function("mk-record", List(NumLit(4)), Some(dt)))))
    
    solver.assert(Predicate("=", 
        List(Function("m", List(x), Some(IntType)), NumLit(4))))
    
    println(solver checkSat)*/
    
    ////////////////////////////////
        
    val rtype:Type = RecordType(List[(String, Type)](
        ("m", IntType), ("n", IntType)))
    
    val expr:Expression = 
    	Record(List[(String, Expression)](
    	    ("m", NumLit(4)), ("n", NumLit(5))), Some(rtype))
    	        	   
    //val expr2 = Eq(Projection(expr, "m", Some(IntType)), NumLit(4))
    
    import ASTImplicits._
    
    def getVar(name:String) = SMTVariable(name, Some(IntType))
    
    def qf(a:Projection) = QuantifiedFormula(EXISTENTIAL, 
        List(("v", IntType)), SMTEquality(a, getVar("v")))
        
    solver.assert(SMTEquality(Id("x", Some(rtype)), expr))
    
    solver.assert(qf(Projection(Id("x", Some(rtype)), "m", Some(IntType))))
    
    solver.assert(qf(Projection(Id("x", Some(rtype)), "n", Some(IntType))))
    
    solver.assert(SMTEquality(Id("x$a", Some(IntType)), 
        Projection(Id("x", Some(rtype)), "m", Some(IntType))))
    
    //solver.assert(expr2)
    
    //println(solver checkSat)
    
    solver.checkSatWithModel match {
      case None => println("unknown")
      case Some((x, m)) =>
        println(x)
      	m match {
          case None => println("no model")
          case Some(y) =>
            println(y.getValue("x$a").get)
            //println(y.getValue("y").get)
        }
    }
    
    /*import ASTImplicits._
    
    val rtype:MyType = RecordType(List[(String, MyType)](("m", MyIntType)))
    
    val expr:Expression = 
    	Record(List[(String, Expression)](("m", MyNumLit(4))), Some(rtype))
    	
    val x:Expression = Id("x", Some(rtype))
    
    solver assert (Eq(x, expr))
   
    val expr2 = Eq(Projection(x, "m", Some(MyIntType)), MyNumLit(4))
    
    print("SMT Result: ")
    
    println(solver checkSatAssum(Set(expr2)))*/
  }
  
  
  ////////////
  
  sealed trait Type
  case object IntType extends Type
  case object BoolType extends Type
  case class RecordType(list:List[(String, Type)]) extends Type
  
  sealed trait Expression {
    def getType():Option[Type]
  }
  
  abstract class AbstractExpression(ttype:Option[Type]) extends Expression {
    def getType():Option[Type] = ttype
  }
  
  case class Id(name:String, ttype:Option[Type]) extends 
  	AbstractExpression(ttype)
  case class NumLit(num:Int) extends AbstractExpression(Some(IntType))
  case class Record(list:List[(String, Expression)], ttype:Option[Type]) 
  	extends AbstractExpression(ttype)
  case class Projection(expr:Expression, label:String, ttype:Option[Type])
  	extends AbstractExpression(ttype)   
  case class Eq(l:Expression, r:Expression)
  	extends AbstractExpression(Some(BoolType))
  
  
  ///////////////
  
  
  object ASTImplicits {
        
    implicit def Type2SMTType(value : Type):SMTType = {
      value match {
       case IntType => SMTIntType
       case BoolType => SMTBoolType
       case RecordType(list) =>
         val name = "Record"
         val cons:Seq[(String, SMTType)] = 
           list.map(y => (y._1, Type2SMTType(y._2))).toSeq
         SMTDataType(name, Seq(("mkRecord", cons)))
      }
    }
    
    import ASTImplicits._
    
    implicit def Expression2SMTFormula(value: Expression):SMTFormula = {
      value match {
        case Eq(l, r) => SMTEquality(l, r)
      }
    }
    
    implicit def Expression2SMTTerm(value: Expression):SMTTerm = {
      value match {
        case x:Id =>
          val t = x.getType
          SMTVariable(x.name, t match  {
            case None => None
            case Some(x) => Some(x)
          })
        case x:NumLit => SMTNumLit(x.num)
        case x:Record => 
          val args = x.list.map(y => Expression2SMTTerm(y._2))
          val t = x.getType
          SMTFunction("mkRecord", args, t match {
            case None => None
            case Some(x) => Some(x)
          })
        case x:Projection =>
          val t = x.getType
          SMTFunction(x.label, List(x.expr), t match {
            case None => None
            case Some(x) => Some(x)
          })
      }
    }
     
  }
  
}