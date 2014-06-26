package scala.smt.visitor

import scala.smt._

class TermFreeVariables extends FreeVariablesVisitor[Term] {
  
  def visit(e:Term, a:Unit = ()):Set[Variable] = {
    e match {
      case x:Variable => Set(x)
      case x:Function =>
        val ts = x.args map(_.getType.get)
        val ft = FunType(ts, x.getType.get)
        x.args.flatMap(visit(_)).toSet + Variable(x.name, Some(ft))
      case x:NumLit => Set()
      case x:BoolLit => Set()
    }
  }
}