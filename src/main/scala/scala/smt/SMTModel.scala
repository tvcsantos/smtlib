package scala.smt

trait SMTModel {
  
  type AST
  
  def getValue(constant:String):Option[AST]
}

object EmptyModel extends SMTModel {
  def getValue(constant:String):Option[AST] = None
}