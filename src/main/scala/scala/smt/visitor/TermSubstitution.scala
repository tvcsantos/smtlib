package scala.smt.visitor

import scala.smt._
import scalax.visitor.SubstitutionVisitor

class TermSubstitution extends SubstitutionVisitor[Term, Term] {

  import scalax.visitor.VisitorException

  def visit(e:Term, a:(String, Term)):Term = {
    val x = a._1
    val t = a._2
    e match {
      case v:Value => v
      case y:Variable => 
        if (y.name == x) t
        else y
      case y:Function =>
        var nn = y.name
        val ft = y.getType
        if (x == y.name) {
	      val v = t.asInstanceOf[Variable]
	      if (v.getType.get.getRefinedType == ft.get.getRefinedType)
	        nn = v.name
        }	      
	    Function(nn, y.args.map(visit(_, (x, t))), ft/*, y.classType*/)
      case x:AbstractTerm =>
        throw new VisitorException(s"Term $x not supported")
    }
  }
}