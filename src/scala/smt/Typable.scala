package scala.smt

trait Typable[T] {  
  def isTyped():Boolean
  
  import scalax.util.Environment
  import visitor._  
  
  def typeCheck(c:TypeChecker[T], e:Environment[Type]):T
  
  def getType():Option[Type]
}