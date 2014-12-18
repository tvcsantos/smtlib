package scala.smt.visitor

import scala.smt._
import scalax.visitor.BoundVariablesVisitor

class FormulaBoundVariables(tv:BoundVariablesVisitor[Term, Identifier])
	extends BoundVariablesVisitor[Formula, Identifier] {
  
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
      case If(c, then, eelse) =>
        visit(c) ++ visit(then) ++ visit(eelse)
      case Let(x, t, b) =>
        (tv visit(t)) ++ visit(b) + Variable(x, t.getType)
      case QuantifiedFormula(q, l, f) =>
        visit(f) ++ (l map(x => Variable(x._1, Some(x._2))))
      case Predicate(n, l/*, _*/) =>
        l.flatMap(tv visit(_)).toSet 
      case Equality(l, r) =>
        (tv visit(l)) ++ (tv visit(r))
      case Distinct(list) =>
        list.flatMap(tv visit(_)).toSet
      case Eqs(set) =>
        set.flatMap(tv visit(_))
    }
  }
}