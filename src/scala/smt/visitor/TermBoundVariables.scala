package scala.smt.visitor

import scala.smt._

class TermBoundVariables extends BoundVariablesVisitor[Term] {
  
  def visit(e:Term, a:Unit = ()):Set[Variable] = {
    e match {
      case x:Variable => Set()
      //case x:BoundVariable => Set()
      case x:Function =>
        x.args.flatMap(visit(_)).toSet
      case x:NumLit => Set()
      case x:BoolLit => Set()
    }
  }
}