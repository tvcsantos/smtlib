package scala.smt

import scalax.ttype.Typable
import scalax.util._
import scalax.visitor.{Visitor, Visitable, TypeChecker}

sealed trait Formula extends Typable[Formula, Type] with
	Visitable[Formula] {
    
  override def toString = {
    import printer.PrettyPrinter._
    asString(this)
  }
  
  def visit[K, L](v:Visitor[Formula, K, L], a:L):K =
    v visit(this, a)
  
  def visit[K, L](a:L)(implicit v:Visitor[Formula, K, L]):K =
    v visit(this, a)
    
  import scala.smt.visitor._
  
  def typeCheck[L](c:TypeChecker[Formula, Type, L], 
      e:(Environment[String, Type], L)):Formula =
    visit(c, e)
}

abstract class AbstractFormula(val ttype:Option[Type]) extends Formula {  
  def getType():Option[Type] = ttype
}

case class BoolFormula(b:Boolean) extends AbstractFormula(Some(BoolType)) {
  def isTyped() = ttype != None
}

case class And(l:Formula, r:Formula) extends AbstractFormula(Some(BoolType)) {
  def isTyped() = ttype != None  && (l isTyped) && (r isTyped)
}

case class Or(l:Formula, r:Formula) extends AbstractFormula(Some(BoolType)) {
  def isTyped() = ttype != None && (l isTyped) && (r isTyped)
}

case class Imp(l:Formula, r:Formula) extends AbstractFormula(Some(BoolType)) {
  def isTyped() = ttype != None && (l isTyped) && (r isTyped)
}

case class Equiv(l:Formula, r:Formula) 
	extends AbstractFormula(Some(BoolType)) {
  def isTyped() = ttype != None && (l isTyped) && (r isTyped)
}

case class Not(f:Formula) extends AbstractFormula(Some(BoolType)) {
  def isTyped() = ttype != None && (f isTyped)
}

case class If(c:Formula, then:Formula, eelse:Formula) 
	extends AbstractFormula(Some(BoolType)) {
  def isTyped() = ttype != None && (c isTyped) && 
		  (then isTyped) && (eelse isTyped)
}

case class Let(x:String, t:Term, in:Formula) 
	extends AbstractFormula(Some(BoolType)) {
  def isTyped() = ttype != None && (t isTyped) && (in isTyped)
}

object Quantifier extends Enumeration {
  type Quantifier = Value
  val UNIVERSAL, EXISTENTIAL = Value
}

import Quantifier._

case class QuantifiedFormula(q:Quantifier, l:List[(String, Type)], f:Formula) 
	extends AbstractFormula(Some(BoolType)) {
  def isTyped() = ttype != None && (f isTyped)
}
    
case class Predicate(name:String, args:List[Term]/*, classType:Option[Type]*/) 
	extends AbstractFormula(Some(BoolType)) {
  def isTyped() = ttype != None && (args forall(_ isTyped))
  
  def arity():Int = args.size
}

case class Equality(l:Term, r:Term) extends AbstractFormula(Some(BoolType)) {
  def isTyped() = ttype != None && (l isTyped) && (r isTyped)
}

case class Distinct(l:List[Variable]) extends AbstractFormula(Some(BoolType)) {
  def isTyped() = ttype != None && (l forall(_ isTyped))
}

case class Eqs(s:Set[Variable]) extends AbstractFormula(Some(BoolType)) {
  def isTyped() = ttype != None && (s forall(_ isTyped))
  
  def expand():Set[Formula] = {
    if (s.isEmpty) Set()
    else {
      val h = s.head
      val t = s.tail
      t.map(y => Equality(h, y)) ++ (Eqs(t) expand)
    }
  } 
}
