package scala.smt

object Variables {
  
  import scala.smt.visitor._
  import scalax.visitor.NamesVisitor
  import scalax.visitor.BoundNamesListVisitor
  import scalax.visitor.Simplifier
  
  def getBoundNameClashes(nv:NamesVisitor[Formula], 
      bnlv: BoundNamesListVisitor[Formula], as: Formula*):Set[String] = {
    import scala.util._
    val bnl = as.flatMap(_ visit(
        new FormulaBoundNamesList(new TermBoundNamesList()), ()))
    val ns = as.flatMap(_ visit(nv, ())).toSet
    (bnl diff(ns.toSeq)).toSet
  }
  
  def hasBoundNameClashes(nv:NamesVisitor[Formula], 
      bnlv: BoundNamesListVisitor[Formula], as: Formula*):Boolean =
    !(getBoundNameClashes(nv, bnlv, as:_*) isEmpty)
    
  def expand(set:Set[Variable], s:Simplifier[Formula]):Set[Set[Formula]] = {
    def expandOneL(l:List[Variable]):Set[Set[Formula]] = {
      l match {
        case Nil => Set()
        case x::Nil => Set()
        case x::y::xs =>
          val rx = expandOneL(x::xs)
          val eq = Equality(x, y)
          val neq = Not(Equality(x, y))
          if (rx.isEmpty) Set(Set(eq), Set(neq))
          else
            rx.map(y => y + eq) ++ rx.map(y => y + neq)         
      }
    }
    def expandAllL(l:List[Variable]):Set[Set[Formula]] = {
      l match {
        case Nil => Set()
        case x::xs =>
        val texp = expandAllL(xs)
        if (texp.isEmpty) expandOneL(x::xs)
        else expandOneL(x::xs).flatMap(a => texp.map(b => a ++ b))
      }
    }
    expandAllL(set.toList).map(_ map(_ visit(s, ())))
  }
}