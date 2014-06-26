package scala.smt.z3

import scala.smt.SMTModel
import z3.scala.Z3Model

class Z3SMTModel(model:Z3Model) extends SMTModel {
  
  type AST = z3.scala.Z3AST
  
  def getValue(constant:String):Option[AST] = {
    model.getModelConstantInterpretation(constant)
  }
  
}