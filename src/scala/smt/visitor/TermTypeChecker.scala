package scala.smt.visitor

import scala.smt._
import scalax.util._

class TermTypeChecker extends TypeChecker[Term] {
  
  def visit(e:Term, a:Environment[Type]):Term = {
    e match {
      case x:BoolLit => x
      case x:NumLit => x
      case x:Variable => (a find x.name) match {
        case None => throw new IdentifierNotFound(x.name)
        case Some(z) => Variable(x.name, Some(z))  
      }
      case x:Function =>
        (a find x.name) match {
          case None => throw new IdentifierNotFound(x.name)
          case Some(z) => 
            if (!z.getType.isInstanceOf[FunType])
            	throw new WrongType(s"${x.name} type must be $FunType")
            val zft = z.getType.asInstanceOf[FunType]
            if (zft.ps.size != x.args.size)
              throw new WrongArgumentsNumber(
                  s"expected ${zft.ps.size} ${if 
                    (zft.ps.size == 1) "argument" 
                    else "arguments" } found ${x.args.size}")
            val nl = x.args.map(visit(_, a))
            zft.ps.zip(nl.map(_.getType.get)).foreach(x => 
              if (x._1.getType != x._2.getType) 
                throw new WrongType(s"expected ${x._1} found ${x._2}")
            )
            Function(x.name, nl, Some(zft.ret))
        }
    }
  }
}