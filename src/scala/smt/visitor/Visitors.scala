package scala.smt.visitor

import scalax.util._
import scala.smt._

trait TypeChecker[T] extends Visitor[T, T, Environment[Type]]

class NamesVisitor[T](fnv:FreeNamesVisitor[T], bnv:BoundNamesVisitor[T]) 
	extends Visitor[T, Set[String], Unit] {
  def visit(e:T, a:Unit = ()):Set[String] =
    (fnv visit(e)) ++ (bnv visit(e))
}

trait FreeNamesVisitor[T] extends Visitor[T, Set[String], Unit] {
  def visit(e:T, a:Unit = ()):Set[String]
}

trait BoundNamesVisitor[T] extends Visitor[T, Set[String], Unit] {
  def visit(e:T, a:Unit = ()):Set[String]
}

class VariablesVisitor[T](fnv:FreeVariablesVisitor[T], 
    bnv:BoundVariablesVisitor[T]) extends Visitor[T, Set[Variable], Unit] {
  def visit(e:T, a:Unit = ()):Set[Variable] =
    (fnv visit(e)) ++ (bnv visit(e))
}

trait FreeVariablesVisitor[T] extends Visitor[T, Set[Variable], Unit] {
  def visit(e:T, a:Unit = ()):Set[Variable]
}

trait BoundVariablesVisitor[T] extends Visitor[T, Set[Variable], Unit] {
  def visit(e:T, a:Unit = ()):Set[Variable]
}

trait Simplifier[T] extends Visitor[T, T, Unit] {
  def visit(e:T, a:Unit = ()):T
}

trait BoundNamesListVisitor[T] extends Visitor[T, List[String], Unit] {
  def visit(e:T, a:Unit = ()):List[String]
}

trait SubstitutionVisitor[T] extends Visitor[T, T, (String, Term)]

class TermBoundNamesList extends BoundNamesListVisitor[Term] {
  def visit(e:Term, a:Unit = ()):List[String] = Nil
}

class FormulaBoundNamesList(tv:BoundNamesListVisitor[Term]) 
	extends BoundNamesListVisitor[Formula] {
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
      case If(c, then, eelse) =>
      	visit(c) ++ visit(then) ++ visit(eelse)
      case Let(x, t, b) =>
      	x :: ((tv visit(t)) ++ visit(b))
      case QuantifiedFormula(q, l, f) =>
      	visit(f) ++ (l map(x => x._1))
      case Predicate(n, l) =>
       	l.flatMap(tv visit(_)) 
      case Equality(l, r) =>
       	(tv visit(l)) ++ (tv visit(r))
      case Distinct(list) =>
        list.flatMap(tv visit(_))
      case Eqs(set) =>
        set.toList.flatMap(tv visit(_))
    }
  }
}