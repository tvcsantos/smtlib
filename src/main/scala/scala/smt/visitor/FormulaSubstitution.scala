package scala.smt.visitor

import scala.smt._
import scalax.visitor.SubstitutionVisitor
import scalax.visitor.FreeNamesVisitor

class FormulaSubstitution(tv:SubstitutionVisitor[Term, Term], 
    fnv:FreeNamesVisitor[Term]) extends SubstitutionVisitor[Formula, Term] {
	def visit(e:Formula, a:(String, Term)):Formula = {
	  val x = a._1
	  val t = a._2
	  e match {
	    case y:BoolFormula => y 
	    case And(l, r) =>
	      And(visit(l, (x, t)), visit(r, (x, t)))
	    case Or(l, r) =>
	      Or(visit(l, (x, t)), visit(r, (x, t)))
	    case Imp(l, r) =>
	      Imp(visit(l, (x, t)), visit(r, (x, t)))
	    case Equiv(l, r) =>
	      Equiv(visit(l, (x, t)), visit(r, (x, t)))
	    case Not(b) => Not(visit(b, (x, t)))
	    case If(c, then, eelse) =>
	      If(visit(c, (x, t)), visit(then, (x, t)), visit(eelse, (x, t)))
	    case Let(y, u, in) =>
	      if (x == y || // replacing bound variable
            ((t visit(fnv, ())) contains(y))) // y \in fn t, y will be bound 
        	Let(y, tv visit(u, (x, t)), in)
          else Let(y, tv visit(u, (x, t)), visit(in, (x, t)))
	    case QuantifiedFormula(q, l, f) =>
	      val tfn = (t visit(fnv, ()))
	      if (l.exists(e => x == e._1) || // replacing bound variable
            l.exists(e => tfn contains(e._1) 
            		/*e._1 \in fn t, e._1 will be bound*/))
	        e
	      else QuantifiedFormula(q, l, visit(f, (x, t)))
	    case Predicate(n, l/*, cty*/) =>
	      var nn = n
	      if (x == n) {
	        val ts = l map(_.getType.get)
	        val ft = FunType(ts, BoolType)
	        val v = t.asInstanceOf[Variable]
	        if (v.getType.get.getRefinedType == ft.getRefinedType)
	          nn = v.name
	      }	      
	      Predicate(nn, l.map(tv visit(_, (x, t)))/*, cty*/)
	    case Equality(l, r) =>
	      Equality(tv visit(l, (x, t)), tv visit(r, (x, t)))
	    case Distinct(list) =>
	      Distinct(list.map(tv.visit(_, (x, t)).asInstanceOf[Variable]))
	    case Eqs(set) =>
	      Eqs(set.map(tv.visit(_, (x, t)).asInstanceOf[Variable]))
	  }	  
	}
}