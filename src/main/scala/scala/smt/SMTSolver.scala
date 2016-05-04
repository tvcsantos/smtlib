package scala.smt

import scalax.util.Env

object SMTSolver {
  import scala.collection.mutable.{
    Map => MutableMap, 
    HashMap => MutableHashMap, 
    Set => MutableSet,
    HashSet => MutableHashSet
  }
  
  import SMTResult._
  
  val cache:MutableMap[Set[Formula], Option[SMTResult]] =
    MutableHashMap[Set[Formula], Option[SMTResult]]()
    
  cache.put(Set[Formula](BoolFormula(true)), Some(SMTResult.SAT))
  cache.put(Set[Formula](BoolFormula(false)), Some(SMTResult.UNSAT))
  
  val modelCache:MutableMap[Set[Formula], Option[SMTModel]] =
    MutableHashMap[Set[Formula], Option[SMTModel]]()
  
  modelCache.put(Set[Formula](BoolFormula(true)), Some(EmptyModel))
  modelCache.put(Set[Formula](BoolFormula(false)), None)
  
}

import scalax.util.Debuggable

trait SMTSolver extends Debuggable {
  import SMTSolver._
  import scala.smt._
  import visitor._
  import SMTResult._
  import SMTExecutionMode._
  
  val DEFAULT_EXEC_MODE = SMTExecutionMode.AUTOMATIC
  
  import scalax.util.StackContext
  import scalax.util.StackCtx
    
  var smtCallCount = 0
     
  var context:StackContext[Formula] = StackCtx[Formula]()
  
  var currentExecMode:SMTExecutionMode = 
    DEFAULT_EXEC_MODE
  
  def setExecutionMode(mode:SMTExecutionMode) =
    currentExecMode = mode
  
  def getExecutionMode() = currentExecMode
  
  // add the Formula to the current
  // context of the SMTSolver. Returns
  // false if the Formula can't be
  // added, that is, if it is a spatial 
  // Formula or if it is not typed!
  def assert(a:Formula):Boolean = {
    if (a isTyped) {
      val fv = a.visit(getFormulaFreeVariablesVisitor(), ())
      val env = Env[String, Type]()
      fv.foreach(x => env.assoc(x.getName, x.getType.get))
      //force type checking to filter late type errors on the SMT
      //println(s"ENV: $env")
      //TODO fix free names with different types: e.g. "="
      //val at = a.typeCheck(getFormulaTypeChecker(), env)
      val at = a
      val ap = at.visit(getFormulaSimplifier(), ())
      context add(ap)
    } else false
  }
  
  protected[smt] def preCheckSat():Unit
  
  protected[smt] def postCheckSat():Unit
    
  def getSmtCallCount() = smtCallCount
  
  def clearDebugImpl() = {
    smtCallCount = 0
  }
  
  // checks if the assertions
  // up to the current context
  // are satisfiable  
  final def checkSat():Option[SMTResult] = {
    val as = context.allElements.filter(_ != BoolFormula(true))
    if (as isEmpty) Some(SMTResult.SAT)
    else {
      val cacheRes = cache.get(as)
      if (cacheRes == None) {
        var res:Option[SMTResult] = None
        if (as contains(BoolFormula(false))) {
          res = Some(SMTResult.UNSAT)
        } else {
          preCheckSat()
          smtCallCount += 1
          /*if (isDebug()) {
            getDebugger().println(as)
          }*/
          res = checkSat(as)
          postCheckSat()
        }
        cache.put(as, res)
        res
      } else {
        cacheRes.get
      }
    }
  }
  
  protected[smt] def checkSat(as:Set[Formula]):Option[SMTResult]
  
  protected[smt] def checkSatWithModel(as:Set[Formula]):
	  Option[(SMTResult, Option[SMTModel])]
    
  // checks if the assertions
  // up to the current context
  // are satisfiable in conjunction with
  // the extra assertions in argument   
  final def checkSatAssum(a:Set[Formula]):Option[SMTResult] = {
    push
    a foreach assert _
    val res = checkSat
    pop
    res
  }

  // checks if the assertions
  // up to the current context
  // are valid
  final def checkValid():Option[Boolean] = {
    val a = context.allElements.
    		foldLeft(BoolFormula(true):Formula)(
    				(r, e) => And(e, r)).visit(getFormulaSimplifier(), ())
    val as = Set(Not(a) visit(getFormulaSimplifier(), ()))
    val cacheRes = cache.get(as)
    if (cacheRes == None) {
      val res = checkValidImpl(a)
      res match {
        case None => 
          cache.put(as, None)
        case Some(x) => {
          var nv:SMTResult = null
          if (x) nv = SMTResult.UNSAT
          else nv = SMTResult.SAT
          cache.put(as, Some(nv))
        }
      }
      res
    } else {
      cacheRes.get match {
        case None => None
        case Some(x) => Some(x == SMTResult.UNSAT)
      }
    }
  }
  
  protected[smt] def newInstance():scala.smt.SMTSolver
  
  protected[smt] final def checkValidImpl(a:Formula):Option[Boolean] = {    
    val contextbk = context
    clearAll
    assert(Not(a) visit(getFormulaSimplifier(), ()))
    val smtR = checkSat()
    val res = smtR match {
      case None => None
      case Some(x) => Some(x == SMTResult.UNSAT)
    }
    context = contextbk
    res
  }
  
  /*protected[smt] final def checkValidImpl(a:Formula):Option[Boolean] = {    
    val solver = newInstance()
    solver assert (Not(a) visit(getFormulaSimplifier(), ()))
    val smtR = solver checkSat()
    val res = smtR match {
      case None => None
      case Some(x) => Some(x == SMTResult.UNSAT)
    }
    res
  }*/
  
  // push a new context to the SMTSolver
  def push() = {
    context = (context pushContext)
  }
  
  // pop the current context
  // if the current context is the last
  // nothing happens
  def pop():Option[Set[Formula]] = {
    val prev = (context popContext)
    prev match { 
      case Some(x) =>
        val res = (context elements)
        context = x
        Some(res)
      case _ =>  None
    }
  }    
  
  // remove all assertions
  // from the current context
  // without poping it
  def clear() = context.clearContext
  
  // remove all assertions
  // and pop all contexts
  def clearAll() = context = StackCtx()
  
  protected[smt] var optTimeout: Option[Long] = None
  
  def setTimeout(timeout: Long): this.type = {
    optTimeout = Some(timeout)
    this
  }
  
  import scalax.visitor.Simplifier
  import scalax.visitor.FreeVariablesVisitor
  import scalax.visitor.FreeNamesVisitor
  import scalax.visitor.TypeChecker
  
  def getFormulaSimplifier():Simplifier[Formula]
  
  //def setFromulaSimplifier(s:Simplifier[Formula])
  
  //def getFormulaSubstitution():SubstitutionVisitor[Formula]
  
  //def setFormulaSubstitution()
  
  def getFormulaFreeVariablesVisitor():
	  FreeVariablesVisitor[Formula, Identifier]
  
  def getFormulaFreeNamesVisitor():
	  FreeNamesVisitor[Formula]
  
  def getFormulaTypeChecker():TypeChecker[Formula, Type, Unit]
    
  def supportModels():Boolean
  
  var model:Boolean = false
  
  final def setModel(b:Boolean) = {
    if (supportModels()) {
      model = b
      changeModel(b)
    }
  }
  
  protected[smt] def changeModel(b:Boolean)
  
  final def getModel():Boolean = model
     
  final def checkSatWithModel():Option[(SMTResult, Option[SMTModel])] = {
    if (!getModel) throw new Exception("models deactivated!")
    val as = context.allElements.filter(_ != BoolFormula(true))
    if (as isEmpty) Some(SMTResult.SAT, Some(EmptyModel))
    else {
      val cacheRes = cache.get(as)
      if (cacheRes == None) {
        var res:Option[(SMTResult, Option[SMTModel])] = None
        if (as contains(BoolFormula(false))) {
          res = Some((SMTResult.UNSAT, None))
        } else {
          preCheckSat()
          res = checkSatWithModel(as)
          postCheckSat()
        }
        res match {
          case None => 
            cache.put(as, None)
          case Some(x) =>
            cache.put(as, Some(x._1))
            modelCache.put(as, x._2)
        }
        //cache.put(as, res)
        res
      } else {
        val smtres = cacheRes.get
        val mres = modelCache.get(as).get
        smtres match {
          case None => None
          case Some(x) => Some((x, mres))
        }
      }
    }
  }
  
  final def checkSatAssumWithModel(a:Set[Formula]):
	  Option[(SMTResult, Option[SMTModel])] = {
    push
    a foreach assert _
    val res = checkSatWithModel
    pop
    res
  }
  
  final def checkSatTemp(as:Set[Formula]):Option[SMTResult] = { 
	val contextbk = context
    clearAll
    as foreach assert _
    val smtR = checkSat()
    context = contextbk
    smtR
    /*val solver = newInstance()
    as foreach(solver assert _)
    solver checkSat()*/
  }
  
  final def checkValidTemp(as:Set[Formula]):Option[Boolean] = {
    val contextbk = context
    clearAll
    as foreach assert _
    val smtR = checkValid()
    context = contextbk
    smtR
    /*val solver = newInstance()
    as foreach(solver assert _)
    solver checkValid()*/
  }
  
  final def checkSatTemp(a:Formula):Option[SMTResult] = 
    checkSatTemp(Set(a))
  
  final def checkValidTemp(a:Formula):Option[Boolean] =
    checkValidTemp(Set(a))
    
}