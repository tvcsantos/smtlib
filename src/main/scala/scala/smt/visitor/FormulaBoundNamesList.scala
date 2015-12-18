package scala.smt.visitor

import scala.smt._

import scalax.visitor.BoundNamesListVisitor

class FormulaBoundNamesList(tv:BoundNamesListVisitor[Term]) 
	extends BoundNamesListVisitor[Formula] {

  import scalax.visitor.VisitorException

  def visit(e:Formula, a:Unit = ()):List[String] = {
    e match {
      case x:BoolFormula => Nil
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
      	x :: ((tv visit(t)) ++ visit(b))
      case QuantifiedFormula(q, l, f) =>
      	visit(f) ++ (l map(x => x._1))
      case Predicate(n, l/*, _*/) =>
       	l.flatMap(tv visit(_)) 
      case Equality(l, r) =>
       	(tv visit(l)) ++ (tv visit(r))
      case Distinct(list) =>
        list.flatMap(tv visit(_))
      case Eqs(set) =>
        set.toList.flatMap(tv visit(_))
      case x:AbstractFormula =>
        throw new VisitorException(s"Formula $x not supported")
    }
  }
}