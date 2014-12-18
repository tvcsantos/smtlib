package scala.smt.typecheck

object TypeChecker {
  
  import scala.smt._
      
  import scala.collection.mutable.{ 
    Map => MutableMap,
    HashMap => MutableHashMap
  }
        
  def subst(t:Type, tv:TypeVariable, c:Type):Type = {
    t match {
      case BoolType => BoolType
      case IntType => IntType
      case FunType(ps, ret) => 
        FunType(ps.map(subst(_, tv, c)), subst(ret, tv, c))
      case DataType(n, cons) =>
        if (n == tv.name) t //n bound in cons
        else DataType(n, 
            cons.map(x => (x._1, x._2.map(y => (y._1, subst(y._2, tv, c))))))
      case x:TypeVariable => 
        if (x == tv) c
        else x
    }
  }
     
  def getTypeHierarchy(t:Type):Set[Type] = {
    var calc:Set[Type] = Set(t)
    var vis:Set[Type] = Set()
    var res:Set[Type] = Set(t)
    do {
      val d = calc.flatMap(_ match {
        case IntType => Set[Type]()
        case BoolType => Set[Type]()
        case FunType(ps, ret) => 
          ps.toSet + ret
        case x:DataType =>
          x.cons.flatMap(y => 
            y._2.map(z => subst(z._2, TypeVariable(x.name), x)))
        case x:TypeVariable => 
          Set[Type]()
      })
      vis = vis ++ calc
      res = res ++ d
      calc = d -- vis
    } while (!(calc isEmpty))
    res
  }
  
  def getGroundTypes(t:Type):Set[Type] = {
    t match {
      case IntType => Set[Type](t)
      case BoolType => Set[Type](t)
      case FunType(ps, ret) => 
        ps.flatMap(getGroundTypes(_)).toSet ++
        getGroundTypes(ret)
      case DataType(n, cons) =>
        cons.flatMap(x => x._2 flatMap(y => 
          getGroundTypes(y._2))).toSet
      case x:TypeVariable => Set[Type](x)
    }
  }
  
  def getTypes(f:Formula):Set[Type] = {
    f match {
      case x:BoolFormula => Set(BoolType)
      case And(l, r) =>
        getTypes(l) ++ getTypes(r) + BoolType
      case Or(l, r) =>
        getTypes(l) ++ getTypes(r) + BoolType
      case Imp(l, r) =>
        getTypes(l) ++ getTypes(r) + BoolType
      case Equiv(l, r) =>
        getTypes(l) ++ getTypes(r) + BoolType
      case Not(b) => getTypes(b) + BoolType
      case If(c, then, eelse) =>
        getTypes(c) ++ getTypes(then) ++ getTypes(eelse)
      case Let(x, t, b) =>
        getTypes(t) ++ getTypes(b)
      case QuantifiedFormula(q, l, qf) =>
        l.map(_._2).toSet ++ getTypes(qf) + BoolType
      case Predicate(_, l/*, _*/) =>
        l.flatMap(getTypes(_)).toSet
      case Equality(l, r) =>
        getTypes(l) ++ getTypes(r)
      case Distinct(list) =>
        list.flatMap(e => getTypes(e)).toSet + BoolType
      case Eqs(set) =>
        set.flatMap(e => getTypes(e)) + BoolType
    }    
  }
  
  def getTypes(t: Term):Set[Type] = {
    t match {
      case x:Variable => Set(x.getType.get)
      //case x:BoundVariable => Set(x.getType.get)
      case x:Function =>
        x.args.flatMap(getTypes(_)).toSet + x.getType.get
      case x:Value => Set(x.getType.get)
    }
  }
  
}