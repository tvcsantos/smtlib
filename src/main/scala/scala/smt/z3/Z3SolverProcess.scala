package scala.smt.z3

import scala.smt.AbstractSMTSolverProcess
import scala.smt.SMTSolver
import scalax.visitor.Simplifier
import scalax.visitor.SubstitutionVisitor
import scalax.visitor.FreeNamesVisitor
import scalax.visitor.FreeVariablesVisitor
import scalax.visitor.TypeChecker
import scala.smt.Formula
import scala.smt.Type
import scala.smt.Term
import scala.smt.Identifier

class Z3SolverProcess(fsimpl:Simplifier[Formula],
    ffn:FreeNamesVisitor[Formula],
    ffv:FreeVariablesVisitor[Formula, Identifier],
    ftc:TypeChecker[Formula, Type, Unit],
    fsubst:SubstitutionVisitor[Formula, Term], bin:String) 
    extends AbstractSMTSolverProcess(fsimpl, ffn, ffv, ftc, fsubst) 
	with SMTSolver {
  
  protected[smt] def newInstance():SMTSolver =
    new Z3SolverProcess(fsimpl, ffn, ffv, ftc, fsubst, bin)
  
  import scala.smt._
  
  import SMTResult._
  
  type AST = String
  type Sort = String
  type SortDef = Seq[FunDef]
  type FunDef = (String, Seq[Sort], Sort)
  type TheoDef = AST
  
  type ADTReference = Sort
  type ADTRefIndex = Sort
  
  type ADTSortDef = (String, SortDef)    
  
  import scalax.util.SeqEnvironment
  import scalax.util.SeqEnv

  protected def getIntSort():Sort = "Int"
  protected def getBoolSort():Sort = "Bool"
  
  protected def mkDataTypeString(e:ADTSortRepr):String = {
    s"(${e._1} ${
      val y = e._2.zip(e._3)
      val res = y.map(z =>
        if (z._2 isEmpty) z._1
        else 
          s"(${z._1} ${z._2.map(w => s"(${w._1} ${w._2})").mkString(" ")})"
      )
      res.mkString(" ")
    })"
  }
  
  protected def mkDataTypesStringImpl(dts:Set[String]):String = {
    s"(declare-datatypes () (${dts.mkString("\n")}))"
  }
  
  protected def mkAssertString(a:AST):String = {
    s"(assert $a)" 
  }
  
  protected def mkAssertsStringImpl(as:Set[String]):String = {
    as.mkString("\n")
  }
  
  protected def mkConstString(c:(String, Sort)):String = {
    s"(declare-const ${c._1} ${c._2})"
  }
  
  protected def mkConstsStringImpl(cs:Set[String]):String = {
    cs.mkString("\n")
  }
  
  protected def mkFunDefString(f:FunDef):String = {
    s"(declare-fun ${f._1} ${f._2.mkString("(", " ", ")")} (${f._3}))"
  }
  
  protected def mkFunDefsStringImpl(fs:Set[String]):String = {
    fs.mkString("\n")
  }
  
  protected def mkTheoDefString(t:TheoDef):String = {
    s"(assert $t)"
  }
  
  protected def mkTheoDefsStringImpl(ts:Set[String]):String = {
    ts.mkString("\n")
  }
  
  protected def mkCheckSatStringOpt():Option[String] = {
    Some("(check-sat)")
  }
    
  protected def mkRegularADTReference(sort:Sort):ADTReference = sort
  
  protected def mkRecursiveADTReference(ref:ADTRefIndex):ADTReference = ref
    
  protected def mkADTSorts(s:Seq[ADTSortRepr]):Seq[ADTSortDef] = {
    s foreach(adtsSet.add _)
    val sm = s.map(x => (x._1, x._2.zip(x._3)))
    sm.map(e => (e._1,
        e._2.map(x => (x._1, x._2.map(y => y._2), e._1)) ++
        e._2.flatMap(x => x._2.map(y => (y._1, Seq(e._1), y._2)))    
      ))
  }
      
  protected def mkADTReference(t:Type, i:Int):ADTRefIndex = {
	  t match {
	    case x:DataType => x.name
	  }    
  }
  
  protected def mapADTSortDef(e:ADTSortDef):TypeDef =
    (e._1, Some((e._2)))
                
  protected final def getNewDefinitions(types:Set[Type], tm:Map[Type, TypeDef], 
      dm:Map[Type, (Sort, Set[FunDef], Set[TheoDef])]):
      Map[Type, (Sort, Set[FunDef], Set[TheoDef])] = {
    dm
  }  
  
  protected def mkConst(name:String, tydef:TypeDef, 
      bc:SeqEnvironment[Type]):AST = {
    constsSet.add((name, tydef._1))
    name
  }
  
  protected def mkFunDef(name:String, argsSorts:Seq[Sort], ret:Sort):FunDef = {
    val fdef = (name, argsSorts, ret)
    funsSet.add(fdef)
    fdef
  }
      
  protected def mkNumLit(num:Int, tydef:TypeDef):AST =
    s"$num"
    
  protected def mkBoolLit(value:Boolean):AST =
    s"$value"
    
  protected def mkFunction(f:FunDef, args:Seq[AST]/*, 
      classType:Option[Sort]*/):AST = {
    /*classType match {
      case None => 
        if (args isEmpty) s"${f._1}"
        else args.mkString(s"(${f._1} ", " ", ")")
      case Some(sort) =>
        if (args isEmpty) s"(as ${f._1} (${sort}))"
        else args.mkString(s"((as ${f._1} (${sort})) ", " ", ")")
    }*/
    if (args isEmpty) s"(as ${f._1} (${f._3}))"
    else args.mkString(s"((as ${f._1} (${f._3})) ", " ", ")")
  }
  
  protected def isBuiltInFunction(x:Function) = {
    x.name match {
      case "+" | "-" | "*" => true
      case _ => false
    }
  }
  
  protected def mkBuiltInFunction(name:String, argsSorts:Seq[Sort], 
      ret:Sort, argsASTs:Seq[AST]):AST = {
    argsASTs.mkString(s"($name ", " ", ")")
  }
  
  protected def mkAnd(seq:Seq[AST]):AST = {
    seq.mkString("(and ", " ", ")")
  }
  
  protected def mkNot(a:AST):AST =
    s"(not $a)"
  
  protected def mkImp(left:AST, right:AST):AST =
    s"(=> $left $right)"
    
  protected def mkEquiv(left:AST, right:AST):AST =
    s"(equiv $left $right)"  
  
  protected def mkDistinct(seq:Seq[AST]):AST = {
    seq.mkString("(distinct ", " ", ")")
  }
    
  protected def mkIf(cond:AST, then:AST, eelse:AST):AST = 
    s"(if $cond $then $eelse)"
    
  protected def mkOr(seq:Seq[AST]):AST = {
    seq.mkString("(or ", " ", ")")
  }
    
  protected def mkBoolFormula(value:Boolean):AST =
    s"$value" 
    
  protected def isBuiltInPredicate(x:Predicate) = {
    x.name match {
      case ">" | "<" | ">=" | "<=" | "=" => true
      case _ => false
    }
  }
  
  protected def mkBuiltInPredicate(name:String, argsSorts:Seq[Sort], 
      ret:Sort, argsASTs:Seq[AST]):AST = {
    name match {
      case ">" | "<" | ">=" | "<=" | "=" =>
        if (argsASTs.length != 2)
          throw new Exception(
              "Relational Predicates have exactly two arguments")
        val l = argsASTs(0)
        val r = argsASTs(1)
        s"($name $l $r)"
      case _ => throw new Exception(s"Unsupported built-in predicate $name!")
    }
  }
  
  protected def mkPredicate(f:FunDef, args:Seq[AST]/*, 
      classType:Option[Sort]*/):AST = {
    /*classType match {
      case None => 
        if (args isEmpty) s"${f._1}"
        else args.mkString(s"(${f._1} ", " ", ")")
      case Some(sort) =>
        if (args isEmpty) s"(as ${f._1} (${sort}))"
        else args.mkString(s"((as ${f._1} (${sort})) ", " ", ")")
    }*/
    if (args isEmpty) s"(as ${f._1} (${f._3}))"
    else args.mkString(s"((as ${f._1} (${f._3})) ", " ", ")")
  }
      
  protected def mkEquality(left:AST, right:AST):AST = {
    s"(= $left $right)"
  }
  
  import Quantifier._
  
  protected def mkQuantifiedFormula(q:Quantifier, 
      l:List[(String, Sort)], f:AST):AST = {
    val bv = l.map(e => s"(${e._1} ${e._2})").mkString("(", " ", ")")
    q match {
      case UNIVERSAL => 
        s"(forall $bv $f)"
      case EXISTENTIAL =>
        s"(exists $bv $f)"
    }
  }
  
  protected def hasSignature(f:FunDef, name:String, args:Seq[Sort], 
      ret:Sort):Boolean = {
    if (f._2.length != args.length) return false
    if (f._1 != name) return false
    for (i <- 0 until f._2.length)
      if (!f._2(i).equals(args(i))) return false
    if (!f._3.equals(ret)) return false
    return true
  }
  
  protected def getFunDef(s:Iterable[TypeDef]):Seq[(Sort, Seq[FunDef])] = {
    import scala.collection.mutable.{
      Set => MutableSet,
      HashSet => MutableHashSet
    }
    var r:MutableSet[(Sort, Seq[FunDef])] = 
    	MutableHashSet[(Sort, Seq[FunDef])]()
    for (e <- s) {
      e._2 match {
        case None => ()
        case Some(x) =>
          //r ++= x
          r += ((e._1, x))
      }
    }
    r.toSeq
  }
               
  protected def processOutput(code:String, 
      out: Stream[String]):Option[SMTResult] = 
    out match {
    case Stream.Empty => None
    case x #:: xs => if (x.toLowerCase contains "unsat") Some(SMTResult.UNSAT)
    	else if (x.toLowerCase contains "sat") Some(SMTResult.SAT)
    	else if (x.toLowerCase contains "timeout") None
    	else if (x.toLowerCase contains "error") 
    	  throw new SMTSolverProcessException(code, s"\n$code\n$x")
    	else processOutput(code, xs)
  }
     
  protected def runSolver(code:String):Stream[String] = {
    val tmpFile = java.io.File.createTempFile("solverCode", ".smt2")
    tmpFile.deleteOnExit()
    val out = new java.io.FileWriter(tmpFile)
    out.write(code)
	out.close
	import scala.sys.process._
	optTimeout match {
      case None => Process(s"$bin ${tmpFile.getAbsolutePath()}").lines
      case Some(x) => Process(s"$bin -T:${x/1000} ${
        tmpFile.getAbsolutePath()}").lines
    }
  }
  
  def supportModels():Boolean = true
  
  def changeModel(b:Boolean) = {}

}