package scala.smt.z3

import scala.smt.AbstractSMTSolver
import scala.smt.SMTSolver

import scala.smt.Formula
import scala.smt.Type
import scala.smt.Identifier
import scala.smt.Term
import scalax.visitor.Simplifier
import scalax.visitor.SubstitutionVisitor
import scalax.visitor.FreeNamesVisitor
import scalax.visitor.FreeVariablesVisitor
import scalax.visitor.TypeChecker

class Z3SolverAPI(fsimpl:Simplifier[Formula],
    ffn:FreeNamesVisitor[Formula],
    ffv:FreeVariablesVisitor[Formula, Identifier],
    ftc:TypeChecker[Formula, Type, Unit],
    fsubst:SubstitutionVisitor[Formula, Term]) 
    extends AbstractSMTSolver(fsimpl, ffn, ffv, ftc, fsubst) with SMTSolver {
  
  protected[smt] def newInstance():SMTSolver =
    new Z3SolverAPI(fsimpl, ffn, ffv, ftc, fsubst)
  
  import z3.scala.{
    Z3AST, Z3Sort, Z3FuncDecl,
    Z3Context, Z3Config
  }
  
  import Z3Context.{
    ADTSortReference, 
    RecursiveType => Z3RecursiveType, 
    RegularSort
  }
  
  import scala.smt._
  import SMTResult._  
  
  type AST = Z3AST
  type Sort = Z3Sort
  type SortDef = (Seq[Z3FuncDecl], Seq[Z3FuncDecl], Seq[Seq[Z3FuncDecl]])
  type FunDef = Z3FuncDecl
  type TheoDef = Z3AST
  
  type ADTReference = ADTSortReference
  type ADTRefIndex = Int 
  
  type ADTSortDef = 
    (Z3Sort, Seq[Z3FuncDecl], Seq[Z3FuncDecl], Seq[Seq[Z3FuncDecl]]) 
    
  import scalax.util.SeqEnvironment
  import scalax.util.SeqEnv
  
  protected val cfg = new Z3Config(/*"MODEL" -> false*/)
  protected val z3ctx = new Z3Context(cfg)
  protected val intSort = z3ctx.mkIntSort
  protected val boolSort = z3ctx.mkBoolSort
  
  protected def getIntSort():Sort = intSort
  protected def getBoolSort():Sort = boolSort
  
  protected[smt] def preCheckSat/*Impl*/():Unit = {
    z3ctx.push
  }
  
  protected[smt] def postCheckSat/*Impl*/():Unit = {
    if (z3ctx.getNumScopes > 0) z3ctx.pop(1)
  }
    
  protected def checkSatImplAuto(as:Set[(Formula, AST)], 
      tm:Map[Type, TypeDef], 
      dm:Map[Type, (Sort, Set[FunDef], Set[TheoDef])]):Option[SMTResult] = {
    dm.foreach(d => d._2._3.foreach(z3ctx.assertCnstr(_)))
    as.foreach(x => z3ctx.assertCnstr(x._2))	
	val r = z3ctx.check match {
      case None => None
      case Some(true) => Some(SMTResult.SAT)
      case Some(false) => Some(SMTResult.UNSAT)
    }
    r
  }
  
  protected def checkSatImplAutoWithModel(as:Set[(Formula, AST)], 
      tm:Map[Type, TypeDef], 
      dm:Map[Type, (Sort, Set[FunDef], Set[TheoDef])]):
      Option[(SMTResult, Option[SMTModel])] = {
    dm.foreach(d => d._2._3.foreach(z3ctx.assertCnstr(_)))
    as.foreach(x => z3ctx.assertCnstr(x._2))
	val r = z3ctx.checkAndGetModel match {
      case (None, _) => None
      case (Some(true), m) => Some(SMTResult.SAT, Some(new Z3SMTModel(m)))
      case (Some(false), _) => Some(SMTResult.UNSAT, None)
    }
    r
  }
    
  protected def mkRegularADTReference(sort:Sort):ADTReference =
    RegularSort(sort)
  
  protected def mkRecursiveADTReference(ref:ADTRefIndex):ADTReference =
    Z3RecursiveType(ref)
    
  protected def mkADTSorts(s:Seq[ADTSortRepr]):Seq[ADTSortDef] = 
    z3ctx.mkADTSorts(s)
   
  protected def mkADTReference(t:Type, i:Int):ADTRefIndex = i 
  
  protected def mapADTSortDef(e:ADTSortDef):TypeDef =
    (e._1, Some((e._2, e._3, e._4)))
             
  protected final def getNewDefinitions(types:Set[Type], tm:Map[Type, TypeDef], 
      dm:Map[Type, (Sort, Set[FunDef], Set[TheoDef])]):
      Map[Type, (Sort, Set[FunDef], Set[TheoDef])] = {
    dm
  }
  
  protected def mkConst(name:String, tydef:TypeDef, 
      bc:SeqEnvironment[Type]):AST = { 
    val r = bc.findIdx(name) 
    r match {
      case None => z3ctx.mkConst(name, tydef._1)
      case Some(x) => z3ctx.mkBound(x, tydef._1)
    }
  }
        
  protected def mkNumLit(num:Int, tydef:TypeDef):AST =
    z3ctx.mkInt(num, tydef._1)
    
  protected def mkBoolLit(value:Boolean):AST = {
    value match {
      case true => z3ctx.mkTrue
      case false => z3ctx.mkFalse
    }    
  }   
    
  protected def mkFunction(f:FunDef, args:Seq[AST]/*, 
      classType:Option[Sort]*/):AST = f(args:_*)
  
  protected def isBuiltInFunction(x:Function) = {
    x.name match {
      case "+" | "-" | "*" => true
      case _ => false
    }
  }
  
  protected def mkBuiltInFunction(name:String, argsSorts:Seq[Sort], 
      ret:Sort, argsASTs:Seq[AST]):AST = {
    name match {
      case "+" => z3ctx.mkAdd(argsASTs:_*)
      case "-" =>
        if (argsASTs.length == 1)
          z3ctx.mkUnaryMinus(argsASTs(0))
        else z3ctx.mkSub(argsASTs:_*)
      case "*" => z3ctx.mkMul(argsASTs:_*)
    }
  }
  
  protected def mkAnd(seq:Seq[AST]):AST =
    z3ctx.mkAnd(seq:_*)
    
  protected def mkNot(a:AST):AST =
    z3ctx.mkNot(a)
    
  protected def mkImp(left:AST, right:AST):AST =
    z3ctx.mkImplies(left, right)
    
  protected def mkEquiv(left:AST, right:AST):AST =
    z3ctx.mkIff(left, right)
    
  protected def mkDistinct(seq:Seq[AST]):AST =
    z3ctx.mkDistinct(seq:_*)
    
  protected def mkIf(cond:AST, then:AST, eelse:AST):AST = 
    z3ctx.mkITE(cond, then, eelse)
    
  protected def mkOr(seq:Seq[AST]):AST =
    z3ctx.mkOr(seq:_*)
  
  protected def mkBoolFormula(value:Boolean):AST = {
    value match {
      case true => z3ctx.mkTrue
      case false => z3ctx.mkFalse
    }
  }
  
  protected def isBuiltInPredicate(x:Predicate) = {
    x.name match {
      case ">" | "<" | ">=" | "<=" | "=" => true
      case _ => false
    }
  }
  
  protected def mkFunDef(name:String, argsSorts:Seq[Sort], ret:Sort):FunDef = {
    z3ctx.mkFuncDecl(name, argsSorts, ret)
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
        name match {
          case ">" => z3ctx.mkGT(l, r)
          case "<" => z3ctx.mkLT(l, r)
          case ">=" => z3ctx.mkGE(l, r)
          case "<=" => z3ctx.mkLE(l, r)
          case "=" => z3ctx.mkEq(l, r)
        }
      case _ => throw new Exception(s"Unsupported built-in predicate $name!")
    }
  }
  
  protected def mkPredicate(f:FunDef, args:Seq[AST]/*, 
      classType:Option[Sort]*/):AST =
    f(args:_*)
      
  protected def mkEquality(left:AST, right:AST):AST = {
    z3ctx.mkEq(left, right)
  }
  
  import Quantifier._
  
  protected def mkQuantifiedFormula(q:Quantifier, 
      l:List[(String, Sort)], f:AST):AST = {
    z3ctx.mkQuantifier(q == Quantifier.UNIVERSAL,
        0, Seq(), l.map(e => (z3ctx.mkStringSymbol(e._1), e._2)), f)
  }
  
  protected def hasSignature(f:FunDef, name:String, args:Seq[Sort], 
      ret:Sort):Boolean = {
    if (f.arity != args.length) return false
    if (f.getName.toString != name) return false
    for (i <- 0 until f.arity)
      if (!f.getDomain(i).equals(args(i))) return false
    if (!f.getRange.equals(ret)) return false
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
          var aux = MutableSet[FunDef]()
          aux ++= x._1
          aux ++= x._2
          for (y <- x._3) aux ++= y
          r += ((e._1, aux.toSeq))
          /*r ++= x._1
          r ++= x._2
          for (y <- x._3) r ++= y*/
      }
    }
    r.toSeq
  }
  
  def supportModels():Boolean = true
  
  def changeModel(b:Boolean) = {
    z3ctx.config.setParamValue("MODEL", b.toString)
  }
  
}