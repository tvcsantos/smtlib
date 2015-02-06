package scala.smt

import scalax.visitor.Simplifier
import scalax.visitor.SubstitutionVisitor
import scalax.visitor.TypeChecker
import scalax.visitor.FreeNamesVisitor
import scalax.visitor.FreeVariablesVisitor

abstract class AbstractSMTSolver(fsimpl:Simplifier[Formula],
    ffn:FreeNamesVisitor[Formula],
    ffv:FreeVariablesVisitor[Formula, Identifier],
    ftc:TypeChecker[Formula, Type, Unit],
    fsubst:SubstitutionVisitor[Formula, Term]) extends SMTSolver {
   
  import scala.collection.mutable.{
    Map => MutableMap, 
    HashMap => MutableHashMap, 
    Set => MutableSet,
    HashSet => MutableHashSet
  }
  
  import SMTResult._
  
  type AST
  type Sort
  type SortDef
  type FunDef
  type TheoDef
  
  type ADTReference
  type ADTRefIndex
  
  final type ADTSortRepr = 
    (String, Seq[String], Seq[Seq[(String, ADTReference)]])
    
  type ADTSortDef
  
  type TypeDef = (Sort, Option[SortDef])
  
  import scalax.util.SeqEnvironment
  import scalax.util.SeqEnv
  
  protected[smt] def checkSat(as:Set[Formula]):Option[SMTResult] = {
    val (tm, dm) = getDefinitions(as)
    val asSeq = as.toSeq
    val bc:SeqEnvironment[Type] = new SeqEnv[Type]() 
    val assmt = asSeq.map(mkAST(_, tm, dm, bc))
    val x = asSeq.zip(assmt)
    checkSatImpl(x.toSet, tm , dm)
  }
  
  protected[smt] def checkSatWithModel(as:Set[Formula]):
	  Option[(SMTResult, Option[SMTModel])] = {
    val (tm, dm) = getDefinitions(as)
    val asSeq = as.toSeq
    val bc:SeqEnvironment[Type] = new SeqEnv[Type]() 
    val assmt = asSeq.map(mkAST(_, tm, dm, bc))
    val x = asSeq.zip(assmt)
    checkSatImplWithModel(x.toSet, tm , dm)
  }
  
  protected def mkRegularADTReference(sort:Sort):ADTReference
  
  protected def mkRecursiveADTReference(ref:ADTRefIndex):ADTReference
  
  protected final def getADTSortReference(t: Type, 
      idxm: Map[Type, ADTRefIndex],
      m:Map[Type, TypeDef]):ADTReference = {
    if (m contains(t)) mkRegularADTReference(m.get(t).get._1)
    else {
      t match {
        case x:TypeVariable => {
          mkRecursiveADTReference(idxm.find(e => e._1 match {
            case y:DataType if (x.name == y.name) => true
            case _ => false
          }).get._2)
        }
        case _ =>
          if (idxm contains(t)) 
            mkRecursiveADTReference(idxm.get(t).get)
          else mkRegularADTReference(m.get(t).get._1)
      }
    }
  }
  
  protected final def mkADTReferenceMap(s:Seq[Type]):Map[Type, ADTRefIndex] = {
    var i = 0
    val zipped = s.map(x => { 
      val res = (x, mkADTReference(x, i))
      i = i + 1
      res 
    })
    Map.empty ++ zipped
  }
  
  protected def mkADTReference(t:Type, i:Int):ADTRefIndex
   
  protected def mkADTSorts(s:Seq[ADTSortRepr]):Seq[ADTSortDef]
  
  protected def mapADTSortDef(e:ADTSortDef):TypeDef
    
  protected final def getRecursiveDataTypes(types:Set[Type], 
      m:Map[Type, TypeDef]):Map[Type, TypeDef] = {
    val ntypes = types.filter(x => !(m contains x))
    val tseq = ntypes.toSeq
    val adts = mkADTSorts(getADTSorts(tseq, m))
    val zipped = tseq.zip(adts)
    val elems = zipped.map(e => (e._1, mapADTSortDef(e._2)))
    m ++ elems
  }
  
  protected final def mkDataType(x:DataType, 
      idxm:Map[Type, ADTRefIndex], m:Map[Type, TypeDef]):ADTSortRepr = {
    import scala.smt.typecheck._
	val ncons = x.cons.map(y => (y._1, y._2.map(z => (z._1, 
	    getADTSortReference(
	        TypeChecker.subst(z._2, TypeVariable(x.name), x), idxm, m)))))
    mkDataTypeImpl(x, ncons)
  }
      
  protected final def mkDataTypeImpl(x:DataType, 
      l:Seq[(String, Seq[(String, ADTReference)])]):ADTSortRepr = {
    val consNames = l.map(_._1)
    val consArgs = l.map(_._2)
    (x.name, consNames, consArgs)
  }
  
  protected final def getADTSorts(s:Seq[Type], m:Map[Type, TypeDef]):
	  Seq[ADTSortRepr] = {
    val idxm = mkADTReferenceMap(s)
    import scala.collection.mutable.ListBuffer
    var res = ListBuffer.empty[ADTSortRepr]
    for (t <- s) {
      t match {
        case x:DataType =>
          res.append(mkDataType(x, idxm, m))
        case _ => ()
      }
    }
    res
  }
  
  protected final def getNewDataTypes(types:Set[Type], 
      tm:Map[Type, TypeDef]):Map[Type, TypeDef] = {
    // remove regular types from 'a' hierarchy
    val rtypes = types.filter(x => x isRegularType)
    val rectypes = types.filter(x => !(x isRegularType))
    val ntm = getRegularDataTypes(rtypes, tm)
    getRecursiveDataTypes(rectypes, ntm)
  }
  
  protected final def getRegularDataTypes(types:Set[Type], 
      tm:Map[Type, TypeDef]):Map[Type, TypeDef] =
    types.foldLeft(tm)((r, e) => getRegularDataType(e, r))
    
  protected final def getRegularDataType(t: Type, 
      m:Map[Type, TypeDef]):Map[Type, TypeDef] = {
    if (m contains t) m else {
      t match {
        case IntType => m + ((t, (getIntSort, None)))
        case BoolType => m + ((t, (getBoolSort, None)))
        case x:FunType => {
          var nm = x.ps.foldLeft(m)(
              (r, e) => getRegularDataType(e, r))
          nm = getRegularDataType(x.ret, nm)
          nm
        }
        case x:DataType => {
          val nm = x.cons.foldLeft(m)((r, e) => 
            e._2.foldLeft(r)((lr, er) => getRegularDataType(er._2, r)))
          val ns = mkADTSorts(Seq(mkDataType(x, Map.empty, nm))).head
          nm + ((t, mapADTSortDef(ns)))
        }
      }
    }
  }
  
  protected def getIntSort():Sort
  protected def getBoolSort():Sort
    
  protected def checkSatImpl(as:Set[(Formula, AST)], tm:Map[Type, TypeDef], 
      dm:Map[Type, (Sort, Set[FunDef], Set[TheoDef])]):Option[SMTResult] =  {
    import SMTExecutionMode._
    currentExecMode match {
      case AUTOMATIC => checkSatImplAuto(as, tm, dm)
      case INTERACTIVE => checkSatImplInteractive(as, tm, dm)
      case MIXED =>
        optTimeout match {
          case Some(to) =>
            checkSatImplAuto(as, tm, dm) match {
              case None => 
                //restartSolver()
                checkSatImplInteractive(as, tm, dm)
              case x => x
            }
          case None =>
            checkSatImplAuto(as, tm, dm)
      }
    }
  }
  
  protected def checkSatImplWithModel(as:Set[(Formula, AST)], 
      tm:Map[Type, TypeDef], 
      dm:Map[Type, (Sort, Set[FunDef], Set[TheoDef])]):
      Option[(SMTResult, Option[SMTModel])] =  {
    import SMTExecutionMode._
    currentExecMode match {
      case AUTOMATIC => checkSatImplAutoWithModel(as, tm, dm)
      case INTERACTIVE => checkSatImplInteractiveWithModel(as, tm, dm)
      case MIXED =>
        optTimeout match {
          case Some(to) =>
            checkSatImplAutoWithModel(as, tm, dm) match {
              case None => 
                //restartSolver()
                checkSatImplInteractiveWithModel(as, tm, dm)
              case x => x
            }
          case None =>
            checkSatImplAutoWithModel(as, tm, dm)
      }
    }
  }
  
  //protected def restartSolver()
  
  protected def checkSatImplAuto(as:Set[(Formula, AST)], 
      tm:Map[Type, TypeDef], 
      dm:Map[Type, (Sort, Set[FunDef], Set[TheoDef])]):Option[SMTResult]
  
  protected def checkSatImplAutoWithModel(as:Set[(Formula, AST)], 
      tm:Map[Type, TypeDef], 
      dm:Map[Type, (Sort, Set[FunDef], Set[TheoDef])]):
      Option[(SMTResult, Option[SMTModel])]
  
  protected def checkSatImplInteractive(as:Set[(Formula, AST)], 
      tm:Map[Type, TypeDef], 
      dm:Map[Type, (Sort, Set[FunDef], Set[TheoDef])]):Option[SMTResult] = {
    Console.out.println(s"${if (as.size <= 1)
      "Is this formula" else "Are these formulas"} satisfiable?")
    as.foreach(x => Console.out.println(x._1))
    readChar match {
      case 'y' => Some(SMTResult.SAT)
      case 'n' => Some(SMTResult.UNSAT)
      case _ => None
    }
  }
  
  protected def checkSatImplInteractiveWithModel(as:Set[(Formula, AST)], 
      tm:Map[Type, TypeDef], 
      dm:Map[Type, (Sort, Set[FunDef], Set[TheoDef])]):
      Option[(SMTResult, Option[SMTModel])] = {
    Console.out.println(s"${if (as.size <= 1)
      "Is this formula" else "Are these formulas"} satisfiable?")
    as.foreach(x => Console.out.println(x._1))
    readChar match {
      //TODO fix this user has to introduce model
      case 'y' => Some(SMTResult.SAT, None)
      case 'n' => Some(SMTResult.UNSAT, None)
      case _ => None
    }
  }
     
  protected final def getDefinitions(as:Set[Formula]):
	  (Map[Type, TypeDef], Map[Type, (Sort, Set[FunDef], Set[TheoDef])]) = {
    val initMap:Map[Type, TypeDef] = 
      Map((IntType, (getIntSort, None)), (BoolType, (getBoolSort, None)))
    val res = as.foldLeft((initMap, 
        Map.empty:Map[Type, (Sort, Set[FunDef], Set[TheoDef])]))(
        (r, e) => ({ getDefinitionsMaps(e, r._1, r._2) }))
    res
  }
  
  protected final def getDefinitionsMaps(a:Formula, tm:Map[Type, TypeDef], 
      dm:Map[Type, (Sort, Set[FunDef], Set[TheoDef])]):
	  (Map[Type, TypeDef], Map[Type, (Sort, Set[FunDef], Set[TheoDef])]) = {
    import typecheck._
    val hie = TypeChecker.getTypes(a).flatMap(_ getHierarchy).filter(
        x => !x.isInstanceOf[TypeVariable])//.toSeq
    val ntm = getNewDataTypes(hie, tm)
    val ndm = getNewDefinitions(hie, ntm, dm)
    //filter all funtype variables
    /*val afv = a.visit(getFormulaFreeVariablesVisitor(), ()).filter(
        e => e.getType().get.isInstanceOf[FunType])*/
    //val uf = Set[FunDef]()
    //val nuf = getNewFunctions(ntm, ndm, uf, afv)
    (ntm, ndm)
  }
  
  protected def getNewDefinitions(types:Set[Type], tm:Map[Type, TypeDef], 
      dm:Map[Type, (Sort, Set[FunDef], Set[TheoDef])]):
    	  	Map[Type, (Sort, Set[FunDef], Set[TheoDef])]
  
  /*protected def getNewFunctions(tm:Map[Type, TypeDef], 
      dm:Map[Type, (Set[FunDef], Set[TheoDef])], uf:Set[FunDef], 
      funs:Set[Variable]):Set[FunDef] = {
    val v:Variable = null
    val ft = v.getType.get.asInstanceOf[FunType]
  }*/
  
  protected def mkConst(name:String, tydef:TypeDef, 
      bc:SeqEnvironment[Type]):AST
      
  protected def mkNumLit(num:Int, tydef:TypeDef):AST
    
  protected def mkBoolLit(value:Boolean):AST
  
  //finds a function/predicate with this signature
  //the signature is composed by the name of the function
  //the type of the arguments and return
  protected final def findSignature(name:String, 
      args:Seq[Sort], ret:Sort, tm:Map[Type, TypeDef], 
      dm:Map[Type, (Sort, Set[FunDef], Set[TheoDef])]/*, classType:Option[Type]*/):
      Option[(Sort, FunDef)] = {
    val s = getFunDef(tm.values)/*if (classType == None) tm.values else 
      Seq(tm.get(classType.get).get))*/
    var r:Option[(Sort, FunDef)] = { 
      val aux = s.find(e => e._2.exists(y => hasSignature(y, name, args, ret)))
      aux match {
        case None => None
        case Some(x) => 
          Some((x._1, x._2.find(e => hasSignature(e, name, args, ret)).get))
      }
    }
    r match {
      case None =>
        var lr:Option[(Sort, FunDef)] = None
        val y = /*if (classType == None)*/ dm.values.map(x => (x._1, x._2)).iterator
        	//else Seq(dm.get(classType.get).get).map(x => (x._1, x._2)).iterator 
        while (y.hasNext && lr == None) {
          val set = y.next
          //lr = set.find(e => hasSignature(e, name, args, ret))
          lr = {
            val aux = s.find(e => 
              	e._2.exists(y => hasSignature(y, name, args, ret)))
            aux match {
              case None => None
              case Some(x) =>
                Some((x._1, 
                    x._2.find(e => hasSignature(e, name, args, ret)).get))
            }
          }
        }
        lr
      case x => x  
    }
  }
  
  protected def hasSignature(f:FunDef, name:String, args:Seq[Sort], 
      ret:Sort):Boolean
  
  protected def getFunDef(s:Iterable[TypeDef]):Seq[(Sort, Seq[FunDef])]
    
  protected def mkFunction(f:FunDef, args:Seq[AST]/*, classType:Option[Sort]*/):AST
      
  protected final def mkAST(t:Term, tm:Map[Type, TypeDef], 
      dm:Map[Type, (Sort, Set[FunDef], Set[TheoDef])], 
      bc:SeqEnvironment[Type]):AST = {
    t match {
      case x if (x isValue) => mkValue(x, tm, dm, bc)
      case x:Variable =>
        mkConst(x.name, (tm get x.getType.get).get, bc)
      case x:Function =>
        val ts = x.args map(_.getType.get)
        val ft = FunType(ts, x.getType.get)
        val rty = ft.ret
        val argsASTs = x.args.map(y => mkAST(y, tm, dm, bc))
        val argsSorts = x.args.map(y => tm.get(y.getType.get).get._1)
        val retSort = tm.get(rty).get._1
        if (isBuiltInFunction(x))
        	mkBuiltInFunction(x.name, argsSorts, retSort, argsASTs)
        else {
          val funOpt = findSignature(x.name, argsSorts, retSort, tm, dm/*, 
              x.classType*/)
          funOpt match {
            case None =>
              mkFunction(mkFunDef(x.name, argsSorts, retSort), argsASTs/*, None*/)
              //throw new Exception(s"Function ${x.name} not defined!")
            case Some(y) => mkFunction(y._2, argsASTs/*, Some(y._1)*/)
          }
        }
    }
  }
  
  //precondition x isValue
  protected final def mkValue(x:Term, tm:Map[Type, TypeDef],
      dm:Map[Type, (Sort, Set[FunDef], Set[TheoDef])], 
      bc:SeqEnvironment[Type]):AST = {
    def mkValueAux(x:Term, t:Type, tm:Map[Type, TypeDef], 
        dm:Map[Type, (Sort, Set[FunDef], Set[TheoDef])]):AST = {
      x match {
        case y:NumLit =>
          mkNumLit(y.num, tm.get(t).get)
        case y:BoolLit => mkBoolLit(y.b)
      }
    }
    val ty = x.getType.get
    ty match {
      /*case y:RecursiveType =>
        mkADTValue(y.tv, mkValueAux(x, y unfold, tm, dm), tm.get(y).get)*/
      case y => mkValueAux(x, y, tm, dm)
    }
  }
      
  protected def mkAnd(seq:Seq[AST]):AST
  
  protected def mkOr(seq:Seq[AST]):AST
  
  protected def mkPredicate(f:FunDef, args:Seq[AST]/*, 
      classType:Option[Sort]*/):AST
  
  protected def mkBoolFormula(value:Boolean):AST
    
  protected def mkNot(a:AST):AST
    
  protected def mkImp(left:AST, right:AST):AST
    
  protected def mkEquiv(left:AST, right:AST):AST
    
  protected def mkDistinct(seq:Seq[AST]):AST
    
  protected def mkIf(cond:AST, then:AST, eelse:AST):AST
  
  protected def mkEquality(left:AST, right:AST):AST
  
  import Quantifier._
  
  protected def mkQuantifiedFormula(q:Quantifier, 
      l:List[(String, Sort)], f:AST):AST
             
  protected final def mkAST(a:Formula, tm:Map[Type, TypeDef],
      dm:Map[Type, (Sort, Set[FunDef], Set[TheoDef])], 
      bc:SeqEnvironment[Type]):AST = {
     a match {
      case BoolFormula(b) => mkBoolFormula(b)
      case And(l, r) => mkAnd(Seq(mkAST(l, tm, dm, bc), mkAST(r, tm, dm, bc)))
      case Or(l, r) => mkOr(Seq(mkAST(l, tm, dm, bc), mkAST(r, tm, dm, bc)))
      case Imp(l, r) => mkImp(mkAST(l, tm, dm, bc), mkAST(r, tm, dm, bc))
      case Equiv(l, r) => mkEquiv(mkAST(l, tm, dm, bc), mkAST(r, tm, dm, bc))
      case Not(b) => mkNot(mkAST(b, tm, dm, bc))
      case If(c, then, eelse) =>
        mkIf(mkAST(c, tm, dm, bc), mkAST(then, tm, dm, bc), 
            mkAST(eelse, tm, dm, bc))
      case Let(x, t, b) =>
        mkAST(b visit(getFormulaSubstitution, (x, t)), tm, dm, bc)
      case QuantifiedFormula(q, l, f) =>
        val nbc = bc.beginScope
        l foreach (nbc assoc _)
        mkQuantifiedFormula(q, 
            l.map(x => (x._1, tm.get(x._2).get._1)), mkAST(f, tm, dm, nbc))
      case x:Predicate =>
        val ts = x.args map(_.getType.get)
        val ft = FunType(ts, BoolType)
        val rty = ft.ret
        val argsASTs = x.args.map(y => mkAST(y, tm, dm, bc))
        val argsSorts = x.args.map(y => tm.get(y.getType.get).get._1)
        val retSort = tm.get(rty).get._1
        if (isBuiltInPredicate(x))
        	mkBuiltInPredicate(x.name, argsSorts, retSort, argsASTs)
        else {
          val funOpt = findSignature(x.name, argsSorts, retSort, tm, dm/*, 
              x.classType*/)
          funOpt match {
            case None =>
              mkPredicate(mkFunDef(x.name, argsSorts, retSort), argsASTs/*, None*/)
              //throw new Exception(s"Predicate ${x.name} not defined!")
            case Some(y) => mkPredicate(y._2, argsASTs/*, Some(y._1)*/)
          }
        }
      case Equality(l, r) =>
        mkEquality(mkAST(l, tm, dm, bc), mkAST(r, tm, dm, bc))
      case Distinct(Nil) => mkBoolFormula(true)
      case Distinct(l) =>
      	mkDistinct(l.map(mkAST(_, tm, dm, bc)))
      case x:Eqs =>
        val y = (x expand)
        if (y.isEmpty) mkBoolFormula(true)
        else mkAnd(y.map(mkAST(_, tm, dm, bc)).toSeq)
    }
  }
  
  protected def mkFunDef(name:String, argsSorts:Seq[Sort], ret:Sort):FunDef
  
  //pre: isBuiltInPredicate
  protected def mkBuiltInPredicate(name:String, argsSorts:Seq[Sort], 
      ret:Sort, argsASTs:Seq[AST]):AST
  
  //pre: isBuiltInFunction
  protected def mkBuiltInFunction(name:String, argsSorts:Seq[Sort], 
      ret:Sort, argsASTs:Seq[AST]):AST
  
  protected def isBuiltInPredicate(x:Predicate):Boolean
  
  protected def isBuiltInFunction(x:Function):Boolean
  
  import scala.smt.visitor._
  
  def getFormulaSimplifier():Simplifier[Formula] = fsimpl
  
  def getFormulaTypeChecker():TypeChecker[Formula, Type, Unit] = ftc
  
  def getFormulaFreeVariablesVisitor():
	  FreeVariablesVisitor[Formula, Identifier] = ffv
  
  def getFormulaSubstitution():SubstitutionVisitor[Formula, Term] = fsubst
  
  def getFormulaFreeNamesVisitor():
	  FreeNamesVisitor[Formula] = ffn
  
}