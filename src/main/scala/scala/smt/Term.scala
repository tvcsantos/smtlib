package scala.smt

import scalax.util._
import scala.smt.visitor.FormulaTypeChecker
import scalax.visitor.Typable
import scalax.visitor.TypeChecker

sealed trait Term extends Typable[Term, Type] with Visitable[Term] {
  override def toString = {
    import printer.PrettyPrinter._
    asString(this)
  }
    
  def isValue():Boolean
  
  def visit[K, L](v:Visitor[Term, K, L], a:L):K = 
    v visit(this, a)
  
  def visit[K, L](a:L)(implicit v:Visitor[Term, K, L]):K =
    v visit(this, a)
    
  import scala.smt.visitor._
  
  def typeCheck[L](c:TypeChecker[Term, Type, L], 
      e:(Environment[String, Type], L)):Term =
    visit(c, e)
}

abstract class AbstractTerm(ttype:Option[Type]) extends Term {
  def isTyped() = ttype != None
  
  def getType():Option[Type] = ttype
}

sealed trait Identifier extends scalax.util.Variable with Term

case class Variable(name:String, ttype:Option[Type]) 
	extends AbstractTerm(ttype) with Identifier {
  def isValue():Boolean = false
  
  def getName():String = name
}

case class Function(name:String, args:List[Term], ttype:Option[Type]/*, 
    classType:Option[Type]*/) 
	extends AbstractTerm(ttype) {
  def airty():Int = args.size
  
  def isValue():Boolean = false
}

sealed trait Value extends Term {
  def isValue():Boolean = true
}

abstract class AbstractValue(ttype:Option[Type]) extends
	AbstractTerm(ttype) with Value

case class NumLit(num:Int) extends AbstractValue(Some(IntType))

case class BoolLit(b:Boolean) extends AbstractValue(Some(BoolType))
