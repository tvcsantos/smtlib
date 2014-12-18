package scala.smt.visitor

import scala.smt._
import scalax.visitor.BoundNamesVisitor

class TermBoundNames extends BoundNamesVisitor[Term] {
  
  def visit(e:Term, a:Unit = ()):Set[String] = {
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