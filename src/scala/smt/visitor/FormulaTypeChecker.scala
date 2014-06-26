package scala.smt.visitor

import scala.smt._
import scalax.util._

abstract class TypeCheckException(msg:String) extends Exception(msg)
  
class WrongType(msg:String) extends TypeCheckException(msg)
 
class IdentifierNotFound(msg:String) extends TypeCheckException(msg)
  
class WrongArgumentsNumber(msg:String) extends TypeCheckException(msg)

class FormulaTypeChecker(tc:TypeChecker[Term]) extends TypeChecker[Formula] {

  import scala.smt._
  
  def visit(e:Formula, a:Environment[Type]):Formula = {
    val env = a
    e match {
      case x:BoolFormula => x
      case And(l, r) =>
        val nl = visit(l, env)
        val nr = visit(r, env)
        if (nl.getType.get.getType != BoolType)
          throw new WrongType(s"$nl type must be bool")
        if (nr.getType.get.getType != BoolType)
          throw new WrongType(s"$nr type must be bool")
        And(nl, nr)
      case Or(l, r) =>
        val nl = visit(l, env)
        val nr = visit(r, env)
        if (nl.getType.get.getType != BoolType)
          throw new WrongType(s"$nl type must be bool")
        if (nr.getType.get.getType != BoolType)
          throw new WrongType(s"$nr type must be bool")
        Or(nl, nr)
      case Imp(l, r) =>
        val nl = visit(l, env)
        val nr = visit(r, env)
        if (nl.getType.get.getType != BoolType)
          throw new WrongType(s"$nl type must be bool")
        if (nr.getType.get.getType != BoolType)
          throw new WrongType(s"$nr type must be bool")
        Imp(nl, nr)
      case Equiv(l, r) =>
        val nl = visit(l, env)
        val nr = visit(r, env)
        if (nl.getType.get.getType != BoolType)
          throw new WrongType(s"$nl type must be bool")
        if (nr.getType.get.getType != BoolType)
          throw new WrongType(s"$nr type must be bool")
        Equiv(nl, nr)
      case Not(b) =>
        val nb = visit(b, env)
        if (nb.getType.get.getType != BoolType)
          throw new WrongType(s"$nb type must be bool")
        Not(nb)
      case If(c, then, eelse) =>
        val nc = visit(c, env)
        if (nc.getType.get.getType != BoolType)
          throw new WrongType(s"$nc type must be bool")
        val nthen = visit(then, env)
        if (nthen.getType.get.getType != BoolType)
          throw new WrongType(s"$nthen type must be bool")
        val nelse = visit(eelse, env)
        if (nelse.getType.get.getType != BoolType)
          throw new WrongType(s"$nelse type must be bool")
        If(nc, nthen, nelse)
      case Let(x, t, b) =>
        val nt = tc visit(t, env)
        val ne = env.beginScope
        ne assoc(x, nt.getType.get)
        val nb = visit(b, ne)
        ne.endScope
        if (nb.getType.get.getType != BoolType)
          throw new WrongType(s"$nb type must be bool")
        Let(x, nt, nb)
      case QuantifiedFormula(q, l, f) =>
        val ne = env.beginScope
        l.foreach(x => ne assoc(x._1, x._2))
        val nf = visit(f, ne)
        ne.endScope
        val ft = nf.getType.get
        if (ft.getType != BoolType)
          throw new WrongType(s"expected body of $BoolType found $ft")
        QuantifiedFormula(q, l, nf)
      case x:Predicate =>
        (env find x.name) match {
          case None => throw new IdentifierNotFound(x.name)
          case Some(z) => 
            if (!z.getType.isInstanceOf[FunType])
            	throw new WrongType(s"${x.name} type must be $FunType")
            val zft = z.getType.asInstanceOf[FunType]
            if (zft.ps.size != x.args.size)
              throw new WrongArgumentsNumber(
                  s"expected ${zft.ps.size} ${if 
                    (zft.ps.size == 1) "argument" 
                    else "arguments" } found ${x.args.size}")
            val nl = x.args.map(tc visit(_, env))
            zft.ps.zip(nl.map(_.getType.get)).foreach(x => 
              if (x._1.getType != x._2.getType) 
                throw new WrongType(s"expected ${x._1} found ${x._2}")
            )
            if (BoolType != zft.ret.getType)	
              throw new WrongType(
                  s"expected $BoolType for return found ${zft.ret}")
            Predicate(x.name, nl)
        }
      case Equality(l, r) =>
        val nl = tc visit(l, env)
        val nr = tc visit(r, env)
        val lt = nl.getType.get
        val rt = nr.getType.get
        if (lt.getType != rt.getType) {
          /*val lt = nl.getType.get
          val rt = nr.getType.get
          val ltgt = lt.getType
          val rtgt = rt.getType*/
          throw new WrongType(s"binary operands must be from the same type")
        }
        Equality(nl, nr)
      case Distinct(list) =>
        val nlist = list map(x => tc.visit(x, env).asInstanceOf[x.type])
        //different type obvious distinct
        Distinct(nlist)
      case x:Eqs =>
        //different type not equal!
        (x expand) foreach(y => visit(y, env))
        Eqs(x.s.map(y => tc.visit(y, env).asInstanceOf[y.type]))
    }
  }
}