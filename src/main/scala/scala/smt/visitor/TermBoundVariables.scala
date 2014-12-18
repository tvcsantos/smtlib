package scala.smt.visitor

import scala.smt._
import scalax.visitor.BoundVariablesVisitor

class TermBoundVariables extends BoundVariablesVisitor[Term, Identifier] {
  
  def visit(e:Term, a:Unit = ()):Set[Identifier] = {
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