package scala.smt

trait Type extends scalax.visitor.Type {
  import typecheck.TypeChecker
  
  def getHierarchy() =
    TypeChecker.getTypeHierarchy(this)
    
  def getGroundTypes() =
    TypeChecker.getGroundTypes(this)
    
  def isRegularType():Boolean =
    getGroundTypes.forall(x => x isBaseType)
    
  override def toString = {
    import printer.PrettyPrinter._
    asString(this)
  } 
}

abstract class AbstractType extends Type {
  def getRefinedType():Type = this
}

case object IntType extends AbstractType {
  def isBaseType():Boolean = true
}

case object BoolType extends AbstractType {
  def isBaseType():Boolean = true
}

case class FunType(ps:List[Type], ret:Type) extends AbstractType {
  def isBaseType():Boolean = false //TODO: is it?
}

case class DataType(name:String, cons: Seq[(String, Seq[(String, Type)])]) 
	extends AbstractType {
  def isBaseType():Boolean = false
}

case class TypeVariable(name:String) extends AbstractType {
  def isBaseType():Boolean = false
}