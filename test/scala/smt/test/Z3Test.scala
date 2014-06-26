package scala.smt.test

object Z3Test {
  
  import z3.scala.{Z3Context, Z3Config}
    import Z3Context.ADTSortReference
    import scala.smt._
    import scala.smt.SMTResult._

    val cfg = new Z3Config("MODEL" -> false/*, "TIMEOUT" -> 2*/)
    val z3ctx = new Z3Context(cfg)
  
  
  def main(args: Array[String]):Unit = {    
    
    
    /*val ast = z3ctx.parseSMTLIB2String("""(declare-const x Int)
(assert (= x (+ 1 2)))
(push)
(assert (exists ((v Int) (w Int)) (= x (+ w v))))""")
	z3ctx.assertCnstr(ast)*/
      
	val intSort = z3ctx.mkIntSort
	
	val boundY = z3ctx.mkBound(0, intSort)
	val boundX2 = z3ctx.mkBound(1, intSort)
	val body2 = z3ctx.mkGT(z3ctx.mkAdd(boundX2, boundY), 
		z3ctx.mkInt(0, intSort))
	val exists2 = z3ctx.mkExists(0, Seq(), 
	    Seq((z3ctx.mkStringSymbol("y"), intSort)), body2)
	
	val boundX = z3ctx.mkBound(0, intSort)
	val body = z3ctx.mkImplies(z3ctx.mkGT(boundX, z3ctx.mkInt(0, intSort)), 
	    exists2)
	val exists = z3ctx.mkExists(0, Seq(), 
	    Seq((z3ctx.mkStringSymbol("x"), intSort)), body)
	z3ctx.assertCnstr(exists)
		
	z3ctx.checkAndGetModel match {
      case (None, _) => println("unknown")
      case (Some(false), _) => println("unsat")
      case (Some(true), m) => 
        println(m)
        println(m.getModelConstantInterpretation("y"))
        m.getModelConstantInterpretations foreach println _
        println(m)
    }
    
  }
}