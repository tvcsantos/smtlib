package scala.smt.visitor

import scala.util._
import scala.smt._
import scalax.visitor.Simplifier

class TermSimplifier extends Simplifier[Term] {
  
  //terms are simplified for now :P
  def visit(e:Term, a:Unit = ()):Term = e
  
}