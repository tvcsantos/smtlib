package scala.smt.visitor

import scala.smt._
import scalax.visitor.Simplifier
import scalax.visitor.FreeNamesVisitor

class FormulaSimplifier(tv: Simplifier[Term], 
    fnv: FreeNamesVisitor[Formula]) extends Simplifier[Formula] {
  
  import Quantifier._
      
  def visit(e:Formula, a:Unit = ()):Formula = {
    e match {
      case x:BoolFormula => x
      case And(l, r) => 
        val ls = visit(l)
        val rs = visit(r)
        (ls, rs) match {
          case (BoolFormula(false), _) => BoolFormula(false)
          case (_, BoolFormula(false)) => BoolFormula(false)
          case (BoolFormula(true), x) => x
          case (x, BoolFormula(true)) => x
          case (x, y) if (x == y) => x
          case (x, And(y, z)) if y == x || z == x => visit(And(y, z))
          case (And(x, y), z) if x == z || y == z => visit(And(x, y))
          case (x, y) => And(x, y)
        }
      case Or(l, r) =>
        val ls = visit(l)
        val rs = visit(r)
        (ls, rs) match {
          case (BoolFormula(true), _) => BoolFormula(true)
          case (_, BoolFormula(true)) => BoolFormula(true)
          case (BoolFormula(false), x) => x
          case (x, BoolFormula(false)) => x
          case (x, y) if (x == y) => x
          case (x, Or(y, z)) if y == x || z == x => visit(Or(y, z))
          case (Or(x, y), z) if x == z || y == z => visit(Or(x, y))
          case (x, y) => Or(x, y)
        }
      case Imp(l, r) =>
        val ls = visit(l)
        val rs = visit(r)
        (ls, rs) match {
          case (BoolFormula(false), _) => BoolFormula(true)
          case (_, BoolFormula(true)) => BoolFormula(true)
          case (x, BoolFormula(false)) => visit(Not(x))
          case (BoolFormula(true), x) => x
          case (x, y) if x == y => BoolFormula(true)
          case (x, y) => Imp(x, y)
        }
      case Equiv(l, r) =>
      	val ls = visit(l)
        val rs = visit(r)
        (ls, rs) match {
          case (x:BoolFormula, y:BoolFormula) if x != y => 
            BoolFormula(false)
          case (x, y) if x == y => BoolFormula(true)
          case (x, y) => Equiv(x, y)
        }
      case Not(f) =>
        visit(f) match {
          case Not(x) => x
          case BoolFormula(true) => BoolFormula(false)
          case BoolFormula(false) => BoolFormula(true)
          case Predicate(">", l::r::Nil/*, cty*/) => Predicate("<=", l::r::Nil/*, cty*/)
          case Predicate("<", l::r::Nil/*, cty*/) => Predicate(">=", l::r::Nil/*, cty*/)
          case Predicate(">=", l::r::Nil/*, cty*/) => Predicate("<", l::r::Nil/*, cty*/)
          case Predicate("<=", l::r::Nil/*, cty*/) => Predicate(">", l::r::Nil/*, cty*/)
          case QuantifiedFormula(UNIVERSAL, l, f) =>
            visit(QuantifiedFormula(EXISTENTIAL, l, Not(f)))
          case QuantifiedFormula(EXISTENTIAL, l, f) =>
            visit(QuantifiedFormula(UNIVERSAL, l, Not(f)))
          case x => Not(x)
        }
      case QuantifiedFormula(q, l, f) =>
        val fs = visit(f)
        val fsfn = fs visit(fnv, ())
        val lred = l filter(e => fsfn contains (e._1))
        if (lred isEmpty) fs
        else QuantifiedFormula(q, lred, fs)
      case Predicate(n, l/*, cty*/) => 
        n match {
          case "=" => 
            if (l.map(_.getType.get).toSet.size > 1) 
              BoolFormula(false) 
            else Predicate(n, l map(tv visit _)/*, cty*/)
          case _ => Predicate(n, l map(tv visit _)/*, cty*/)
        }
      case Equality(l, r) =>
        val ls = tv visit(l)
        val rs = tv visit(r)
        (ls, rs) match {
          case (x, y) if x == y => BoolFormula(true)
          case (x, y) => {
            if (x.getType.get != y.getType.get)
              BoolFormula(false)
            else Equality(x, y)
          }
        }
      case y:Distinct => 
        if (y.l.size <= 1)
          // only one or less variable of course
          // they are distinct from the others!
          BoolFormula(true)
        else {
          implicit object VariableOrdering extends Ordering[Variable] {
            def compare(x: Variable, y: Variable): Int = 
              x.name.compareTo(y.name)
          }
          if (y.l.toSet.size == y.l.size) {
            // does not contain repeated ids
            import scala.util.Sorting._
            val res:Array[Variable] = y.l.toArray[Variable]
            quickSort(res)
            Distinct(res.toList)
          } else BoolFormula(false)
        }
      case y:Eqs =>
        if (y.s.size <= 1) 
          BoolFormula(true)
        else if (y.s.size > 1) {
          val e = y.s.head
          if (y.s.exists(x => x.getType.get != e.getType.get)) {
            //all ids must have the same type
            //otherwise they can't be equal
            BoolFormula(false)
          } else if (y.s.size == 2) {
            Equality(y.s.head, y.s.tail.head)
          } else y
        } else y
      case y => y
    }
  }
}