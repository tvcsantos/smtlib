package scala.smt

object Substitution {
  
  /*def unfold(rec:Recursor, a:Assertion):Assertion = {
    a match {
      case y:BoolA => y
      case If(c, then, eelse) => 
        If(c, unfold(rec, then), unfold(rec, eelse))
      case Let(y, u, in) =>
        if (rec.rv == y || // replacing bound variable
            ((rec fn) contains(y))) // y \in fn rec, y will be bound 
        	Let(y, u, in)
        else Let(y, u, unfold(rec, in))
      case LetDeref(y, z, in) =>
        if (rec.rv == y || // replacing bound variable
            ((rec fn) contains(y))) // y \in fn rec, y will be bound
          LetDeref(y, z, in)
        else LetDeref(y, z, unfold(rec, in))
      case Sep(l, r) =>
        Sep(unfold(rec, l), unfold(rec, r))
      case And(l, r) =>
        And(unfold(rec, l), unfold(rec, r))
      case SpatAnd(l, r) =>
        SpatAnd(unfold(rec, l), unfold(rec, r))
      case Not(b) =>
        Not(unfold(rec, b))
      case Emp => Emp
      case x:Relational => x
      case x:Cond => x
      case Imp(l, r) =>
        Imp(unfold(rec, l), unfold(rec, r))
      case Equiv(l, r) =>
        Equiv(unfold(rec, l), unfold(rec, r))
      case x:DistinctIds => x
      case x:EqIds => x
      case RecApp(b, l) =>
        RecApp(unfold(rec, b), l)
      case x:RecVar =>
        if (x.rv == rec.rv) rec
        else x
      case Recursor(rv, l, b, ty) =>
        if (rv == rec.rv || l.exists(_._1 == rec.rv)) 
          a
        else {
          Recursor(rv, l, unfold(rec, b), ty)
        }
    }
  }*/
  
}