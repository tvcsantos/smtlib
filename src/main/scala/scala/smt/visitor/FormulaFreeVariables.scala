package scala.smt.visitor

import scala.smt._
import scalax.visitor.FreeVariablesVisitor

class FormulaFreeVariables(tv:FreeVariablesVisitor[Term, Identifier])
	extends FreeVariablesVisitor[Formula, Identifier] {

  import scalax.visitor.VisitorException

  def visit(e:Formula, a:Unit = ()):Set[Identifier] = {
    e match {
      case x:BoolFormula => Set()
      case And(l, r) =>
        visit(l) ++ visit(r)
      case Or(l, r) =>
        visit(l) ++ visit(r)
      case Imp(l, r) =>
        visit(l) ++ visit(r)
      case Equiv(l, r) =>
        visit(l) ++ visit(r)
      case Not(b) => visit(b)
      case If(c, tthen, eelse) =>
        visit(c) ++ visit(tthen) ++ visit(eelse)
      case Let(x, t, b) =>
        val xid = Variable(x, Some(t.getType.get))
        (tv visit(t)) ++ (visit(b) - xid)
      case QuantifiedFormula(q, l, f) =>
        visit(f) -- (l map(x => Variable(x._1, Some(x._2))))
      case Predicate(n, l/*, _*/) =>
        val ts = l map(_.getType.get)
        val ft = FunType(ts, BoolType)
        l.flatMap(tv visit(_)).toSet + Variable(n, Some(ft)) 
      case Equality(l, r) =>
        (tv visit(l)) ++ (tv visit(r))
      case Distinct(list) =>
        list.flatMap(tv visit(_)).toSet
      case Eqs(set) =>
        set.flatMap(tv visit(_))
      case x:AbstractFormula =>
        throw new VisitorException(s"Formula $x not supported")
    }
  }
}