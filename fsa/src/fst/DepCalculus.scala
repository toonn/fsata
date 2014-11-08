package fst

import Syntax._

/**
 * This is the solution template for your dependently typed calculus. 
 * 
 * @author Akkermans Sven and Nolten Toon
 */
class DepCalculus extends Calculus[Term,Term,Unit] {
  
  type Term = Syntax.Term
  
  val parser = new DepParser(this);
  val eval = new Evaluator();
  
  // TODO: implement
  // essentials
  override def mkVar(i : Int) = Var(i)
  override def mkAbs(v: String, ty: Option[Term], t: Term) = Lam(v,ty,t)
  override def mkApp(f : Term, a : Term) = App(f,a)
  
  override def mkLet(v: String, ty: Term, vi: Term, t: Term) : Term = notImplemented

  override def mkTArr(t1 : Term, t2: Term) = notImplemented
  override def mkPi(v: String, t1: Term, t2: Term) = Pi(v, t1, t2)
  override def mkSet = Set
  
  override def mkAnnot(ty: Term, t: Term) = Ann(ty,t)
  
  // booleans
  override def mkBool = notImplemented
  override def mkTrue = notImplemented
  override def mkFalse = notImplemented
  override def mkIfThenElse(c: Term, e1: Term, e2: Term) = notImplemented
  
  // naturals
  override def mkNat = notImplemented
  override def mkZero = notImplemented
  override def mkSucc(e: Term) = notImplemented
  override def mkPred(e: Term) = notImplemented
  override def mkIsZero(e: Term) = notImplemented
  override def mkNatInd = notImplemented
  
  // unit type
  override def mkTUnit = notImplemented
  override def mkUnit = notImplemented
  
  // sigma types
  override def mkSigma(v: String, a: Term, b: Term) : Term = notImplemented
  override def mkPair(x: Term, y: Term) : Term = notImplemented
  override def mkFirst(t: Term) : Term = notImplemented
  override def mkSecond(t: Term) : Term = notImplemented
    
  // singleton types
  override def mkI = notImplemented
  override def mkRefl = notImplemented
  override def mkSubst = notImplemented
  
  // dependent if
  override def mkBoolElim = notImplemented
  
  
  //SAN: Added a couple of possible solution templates but I'm unsure of the correct implementation in Scala. No examples...
  //	Hence, I'll do only some because I would want to test them first.
  def churchBoolDefinition =  """TODO"""
    // true Lam(t, None, Lam(f, None, t))
  def truDefinition = """TODO"""
    // fls Lam(t, None, Lam(f, None, f))
  def flsDefinition = """TODO"""
    // not Lam(a, None, Lam(t, None, Lam(f, None, Lam( Lam(a,None,f),t))))
  def notDefinition = """TODO"""
    // and Lam(a, None, Lam(b, None, Lam(Lam(a,None,b), a))))
  def andDefinition = """TODO"""
    // or Lam(a, None, Lam(b, None, Lam( Lam(a, None, a), b))))
  def orDefinition = """TODO"""
  def boolEqDefinition = """TODO"""
    
  def churchNatDefinition = """TODO"""
  def zeDefinition = """TODO"""
  def suDefinition = """TODO"""
  def isZeroDefinition = """TODO"""
  def plusDefinition = """TODO"""
    
  // If you make the optional exercise to define times using the natInd primitive, do it here...
  def timesDefinition = """TODO"""
  // If you make the optional exercise to define pred2 using the natInd primitive, do it here...
  def pred2Definition = """TODO"""
  // If you make the optional exercise to define the proof that 0 is a right zero for the function plus 
  // (assume that plus is already defined)
  def proofTerm = """TODO"""
  // If you make the optional exercise to construct a value of type ((b : Bool) -> if b then Nat else Bool) 
  // using the boolElim primitive, do it here...
  def ifXThenNatElseBoolDefinition = """TODO"""
}