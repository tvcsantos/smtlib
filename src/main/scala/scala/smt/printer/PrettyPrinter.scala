package scala.smt.printer

object PrettyPrinter {
  import scala.smt._
   
  def asString(f: Formula): String = f match {
    case BoolFormula(b) => s"$b"
    case And(l, r)  => pf"$l and $r"
    case Or(l, r)  => pf"$l or $r"
    case Imp(l, r) => pf"$l => $r"
    case Equiv(l, r) => pf"$l <=> $r"
    case Not(f) => pf"not $f"
    case If(c, tthen, eelse) => pf"if $c then $tthen else $eelse"
    case Let(x, t, in) => s"let $x = " + pt"$t in " + pf"$in" 
    case QuantifiedFormula(q, l, f) =>
      import Quantifier._
      val qs = q match {
        case UNIVERSAL => "forall"
        case EXISTENTIAL => "exists"
      }
      l match {
        case Nil => pf"$f"
        case y => 
          val head = y.head
          val tail = y.tail
          val ls = tail.foldLeft(s"${head._1}:${pty"${head._2}"}")((r, e) =>
          	r + s", ${e._1}:${pty"${e._2}"}")
          s"$qs $ls. (${pf"$f"})"
      }
    case Predicate(n, l/*, _*/) =>
      l match {
        case Nil => s"$n()"
        case y => 
          val head = y.head
          val tail = y.tail
          val ls = tail.foldLeft(pt"${head}")((r, e) => r + pt", ${e}")
          s"$n($ls)"
      }
    case Equality(l, r) => pt"$l = $r"
    case Distinct(l) if l isEmpty => "distinct()"
    case Distinct(l) => {
      val x = l.head
      val xs = l.tail
      pt"distinct($x" + xs.foldLeft("")((r, e) => r + pt", $e") + ")"
    }
    case Eqs(s) if s isEmpty => "eq()"
    case Eqs(s) => {
      val x = s.head
      val xs = s.tail
      pt"eq($x" + xs.foldLeft("")((r, e) => r + pt", $e") + ")"
    }
  }
  
  def asString(t: Term): String = t match {
    case x:Variable => x.name
    //case x:BoundVariable => x.name
    case Function(n, l, _/*, _*/) =>
      l match {
        case Nil => s"$n()"
        case y => 
          val head = y.head
          val tail = y.tail
          val ls = tail.foldLeft(pt"${head}")((r, e) => r + pt", ${e}")
          s"$n($ls)"
      }
    /*case x:Id =>
      s"${x.name}"/*${x.getType match {
        case None => ""
        case Some(ty) => pty":$ty"
      }}"*/*/
    case NumLit(n) => n toString
    case BoolLit(b) => b toString
    case x:AbstractTerm =>
      throw new Exception(s"Term $x not supported")
  }
  
  def asString(ty: Type): String = ty match {
    case IntType => "Int"
    case BoolType => "Bool"
    case FunType(ps, ret) =>
      s"${ps.mkString("(", ", ", ")")} -> ${pty"$ret"}"
    case DataType(n, c) => 
      s"DataType($n, $c)"
      /*if (c isEmpty) {
        s"$n"
      } else {
        val head = c.head
        val tail = c.tail
        if (head._2 isEmpty)
          s"${head._1}"
        else {
          
        }
        val ls = tail.foldLeft(head._1)((r, e) => r + pt", ${e}")        
      }*/
    case TypeVariable(tv) => s"$tv"
  }
 
  private implicit class PrettyPrinting(val sc: StringContext) {
    def pf(args: Formula*) = sc.s((args map parensIfNeeded):_*)
    def pt(args: Term*) = sc.s((args map parensIfNeeded):_*)
    def pty(args: Type*) = sc.s((args map parensIfNeeded):_*)
  }
 
  private def parensIfNeeded(a: Formula) = a match {
    case BoolFormula(b) => asString(a)
    case _  => "(" + asString(a) + ")"
  }
 
  private def parensIfNeeded(t: Term) = t match {
    case x:Variable => asString(x)
    //case x:BoundVariable => asString(x)
    case x:NumLit => asString(x)
    case x:BoolLit => asString(x)
    case _ => "(" + asString(t) + ")"
  }
  
  private def parensIfNeeded(ty: Type) = ty match {
    case _ => asString(ty)
  }
}
