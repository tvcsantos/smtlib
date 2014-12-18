package scala.smt

import scalax.visitor.Simplifier
import scalax.visitor.SubstitutionVisitor
import scalax.visitor.FreeNamesVisitor
import scalax.visitor.FreeVariablesVisitor
import scalax.visitor.TypeChecker

abstract class AbstractSMTSolverProcess(fsimpl:Simplifier[Formula],
    ffn:FreeNamesVisitor[Formula],
    ffv:FreeVariablesVisitor[Formula, Identifier],
    ftc:TypeChecker[Formula, Type, Unit],
    fsubst:SubstitutionVisitor[Formula, Term]) 
    extends AbstractSMTSolver(fsimpl, ffn, ffv, ftc, fsubst) {
  
  import SMTResult._
  
  import scala.collection.mutable.{
    Map => MutableMap, 
    HashMap => MutableHashMap, 
    Set => MutableSet,
    HashSet => MutableHashSet
  }
  
  var constsSet:MutableSet[(String, Sort)] = 
    MutableHashSet[(String, Sort)]()
  var adtsSet:MutableSet[ADTSortRepr] =
    MutableHashSet[ADTSortRepr]()
  var funsSet:MutableSet[FunDef] = 
    MutableHashSet[FunDef]() 
    
  protected[smt] def preCheckSat() = {
    constsSet.clear
    adtsSet.clear
    funsSet.clear
  }
  
  protected[smt] def postCheckSat() = {
  }
  
  protected final def mkDataTypesString(adts:Set[ADTSortRepr]):
	  Option[String] = {
    if (adts isEmpty) None
    else Some(mkDataTypesStringImpl(adts.map(mkDataTypeString(_))))
  }
  
  protected final def mkAssertsString(as:Set[AST]):Option[String] = {
    if (as isEmpty) None
    else Some(mkAssertsStringImpl(as.map(mkAssertString(_))))
  }
  
  protected final def mkConstsString(cs:Set[(String, Sort)]):Option[String] = {
    if (cs isEmpty) None
    else Some(mkConstsStringImpl(cs.map(mkConstString(_))))
  }
  
  protected final def mkFunDefsString(fs:Set[FunDef]):Option[String] = {
    if (fs isEmpty) None
    else Some(mkFunDefsStringImpl(fs.map(mkFunDefString(_))))
  }
  
  protected final def mkTheoDefsString(ts:Set[TheoDef]):Option[String] = {
    if (ts isEmpty) None
    else Some(mkTheoDefsStringImpl(ts.map(mkTheoDefString(_))))
  }
  
  protected def mkDataTypeString(e:ADTSortRepr):String
  
  protected def mkDataTypesStringImpl(dts:Set[String]):String
  
  protected def mkAssertString(a:AST):String
  
  protected def mkAssertsStringImpl(as:Set[String]):String
  
  protected def mkConstString(c:(String, Sort)):String
  
  protected def mkConstsStringImpl(cs:Set[String]):String
  
  protected def mkFunDefString(f:FunDef):String
  
  protected def mkFunDefsStringImpl(fs:Set[String]):String
  
  protected def mkTheoDefString(t:TheoDef):String
  
  protected def mkTheoDefsStringImpl(ts:Set[String]):String
  
  protected def mkCheckSatStringOpt():Option[String]
  
  protected def checkSatImplAuto(bs:Set[(Formula, AST)], 
      tm:Map[Type, TypeDef],
      dm:Map[Type, (Sort, Set[FunDef], Set[TheoDef])]):Option[SMTResult] = {
    
    import scala.collection.mutable.ListBuffer
    
    val list:ListBuffer[Option[String]] = ListBuffer()
    
    list append(mkDataTypesString(adtsSet.toSet))
    
    list append(mkFunDefsString(funsSet.toSet))
    
    list append(mkConstsString(constsSet.toSet))
    
    val dmValues = dm.values.toSet
    
    val fs = dmValues.map(_._2)
    
    fs.foreach(x => list.append(mkFunDefsString(x)))
    
    val ts = dmValues.map(_._3)
    
    ts.foreach(x => list.append(mkTheoDefsString(x)))
    
    list append(mkAssertsString(bs.map(_._2)))
    
    list append(mkCheckSatStringOpt)
    
    val code = list.filter(_ != None).map(_.get).mkString("\n")
	
	runSMT(code)
  }
  
  protected def checkSatImplAutoWithModel(bs:Set[(Formula, AST)], 
      tm:Map[Type, TypeDef],
      dm:Map[Type, (Sort, Set[FunDef], Set[TheoDef])]):
      Option[(SMTResult, Option[SMTModel])] = {
    
    import scala.collection.mutable.ListBuffer
    
    val list:ListBuffer[Option[String]] = ListBuffer()
    
    list append(mkDataTypesString(adtsSet.toSet))
    
    list append(mkConstsString(constsSet.toSet))
    
    val dmValues = dm.values.toSet
    
    val fs = dmValues.map(_._2)
    
    fs.foreach(x => list.append(mkFunDefsString(x)))
    
    val ts = dmValues.map(_._3)
    
    ts.foreach(x => list.append(mkTheoDefsString(x)))
    
    list append(mkAssertsString(bs.map(_._2)))
    
    list append(mkCheckSatStringOpt)
    
    val code = list.filter(_ != None).map(_.get).mkString("\n")
	
    //TODO fix must parse the model....
	runSMT(code) match {
      case None => None
      case Some(x) => Some(x, None)
    }
  }

  protected def processOutput(code:String, 
      out: Stream[String]):Option[SMTResult]
  
  protected def runSMT(code:String):Option[SMTResult] = 
    processOutput(code, runSolver(code))
    
  protected def runSolver(code:String):Stream[String]
}