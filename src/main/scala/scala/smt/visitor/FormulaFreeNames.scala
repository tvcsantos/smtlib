package scala.smt.visitor

import scala.smt._
import scalax.visitor.FreeNamesVisitor

class FormulaFreeNames(tv:FreeNamesVisitor[Term])
	extends FreeNamesVisitor[Formula] {
  
  def visit(e:Formula, a:Unit = ()):Set[String] = {
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
      case If(c, then, eelse) =>
        visit(c) ++ visit(then) ++ visit(eelse)
      case Let(x, t, b) =>
        (tv visit(t)) ++ (visit(b) - x)
      case QuantifiedFormula(q, l, f) =>
        visit(f) -- (l map(x => x._1))
      case Predicate(n, l/*, _*/) =>
        //val ts = l map(_.getType.get)
        //val ft = FunType(ts, BoolType)
        l.flatMap(tv visit(_)).toSet + n
      case Equality(l, r) =>
        (tv visit(l)) ++ (tv visit(r))
      case Distinct(list) =>
        list.flatMap(tv visit(_)).toSet
      case Eqs(set) =>
        set.flatMap(tv visit(_))
    }
  }
}