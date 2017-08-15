package scala.smt.visitor

import scala.smt.Term
import scalax.visitor.BoundNamesListVisitor

class TermBoundNamesList extends BoundNamesListVisitor[Term] {
  def visit(e:Term, a:Unit = ()):List[String] = Nil
}