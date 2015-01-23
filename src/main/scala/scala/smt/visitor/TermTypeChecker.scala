package scala.smt.visitor

import scalax.util.Environment
import scala.smt._
import scalax.visitor.TypeChecker
import scalax.visitor.WrongType
import scalax.visitor.WrongArgumentsNumber
import scalax.visitor.NameNotFound

class TermTypeChecker extends TypeChecker[Term, Type, Unit] {

  def getTypeExpander() =
    //FIXME type expander for smt solver is not defined
    throw new Exception("not defined for this class!")
  
  def visit(e:Term, a:(Environment[String, Type], Unit)):Term = {
    e match {
      case x:BoolLit => x
      case x:NumLit => x
      case x:Variable => (a._1 find x.name) match {
        case None => throw new NameNotFound(x.name, x.name)
        case Some(z) => Variable(x.name, Some(z))  
      }
      case x:Function =>
        (a._1 find x.name) match {
          case None => throw new NameNotFound(x.name, x.name)
          case Some(z) => 
            if (!z.getRefinedType.isInstanceOf[FunType])
            	throw new WrongType(s"${x.name} type must be $FunType")
            val zft = z.getRefinedType.asInstanceOf[FunType]
            if (zft.ps.size != x.args.size)
              throw new WrongArgumentsNumber(
                  s"expected ${zft.ps.size} ${if 
                    (zft.ps.size == 1) "argument" 
                    else "arguments" } found ${x.args.size}")
            val nl = x.args.map(visit(_, a))
            zft.ps.zip(nl.map(_.getType.get)).foreach(x => 
              if (x._1.getRefinedType != x._2.getRefinedType) 
                throw new WrongType(s"expected ${x._1} found ${x._2}")
            )
            Function(x.name, nl, Some(zft.ret)/*, x.classType*/)
        }
    }
  }
}