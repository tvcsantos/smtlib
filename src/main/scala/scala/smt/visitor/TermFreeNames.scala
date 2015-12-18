package scala.smt.visitor

import scala.smt._
import scalax.visitor.FreeNamesVisitor

class TermFreeNames extends FreeNamesVisitor[Term] {

  import scalax.visitor.VisitorException
  
  def visit(e:Term, a:Unit = ()):Set[String] = {
    e match {
      case x:Variable => Set(x.name)
      case x:Function =>
        x.args.flatMap(visit(_)).toSet + x.name
      case x:NumLit => Set()
      case x:BoolLit => Set()
      case x:AbstractTerm =>
        throw new VisitorException(s"Term $x not supported")
    }
  }
}