package scala.smt.visitor

import scala.smt._
import scalax.visitor.FreeVariablesVisitor

class TermFreeVariables extends FreeVariablesVisitor[Term, Identifier] {

  import scalax.visitor.VisitorException
  
  def visit(e:Term, a:Unit = ()):Set[Identifier] = {
    e match {
      case x:Variable => Set(x)
      case x:Function =>
        val ts = x.args map(_.getType.get)
        val ft = FunType(ts, x.getType.get)
        x.args.flatMap(visit(_)).toSet + Variable(x.name, Some(ft))
      case x:NumLit => Set()
      case x:BoolLit => Set()
      case x:AbstractTerm =>
        throw new VisitorException(s"Term $x not supported")
    }
  }
}