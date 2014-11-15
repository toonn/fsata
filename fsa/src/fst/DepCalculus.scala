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
  override def mkBool = Bool
  override def mkTrue = True
  override def mkFalse = False
  override def mkIfThenElse(c: Term, e1: Term, e2: Term) = IfThenElse(c,e1,e2)
  
  // naturals
  override def mkNat = Nat
  override def mkZero = Zero
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
    
  // singleton types \\SAN: Optional
  override def mkI = notImplemented
  override def mkRefl = notImplemented
  override def mkSubst = notImplemented
  
  // dependent if //SAN: Optional
  override def mkBoolElim = notImplemented
  
  
  //SAN: Added a couple of possible solution templates but I'm unsure of the correct implementation in Scala. No examples...
  //	Hence, I'll do only some because I would want to test them first.
  
  //TODO
  def churchBoolDefinition =  """\b . b true false"""
    
    // true Lam(t, None, Lam(f, None, t))
  def truDefinition = """\t . \f . t"""
    // fls Lam(t, None, Lam(f, None, f))
  def flsDefinition = """\t . \f . f"""
    // not Lam(a, None, Lam(t, None, Lam(f, None, App( App(a,f), t))))
  def notDefinition = """\a . \t . \f . ( (a, f), t )"""
    // and Lam(a, None, Lam(b, None, App(App(a,b), a))))
  def andDefinition = """\\a . \b . ( (a, b), a)"""
    // or Lam(a, None, Lam(b, None, App( App(a, a), None, b))))
  def orDefinition = """\a . \b . ( (a , a), b)"""
    
  // TODO
  def boolEqDefinition = """TODO"""
  // TODO  
  def churchNatDefinition = """TODO"""
    
  // Zero Lam(n, None, Lam (s, None, s)
  def zeDefinition = """\n . \s . s"""
  // Succ	Lam( n, None, Lam(s, None, Lam (z, None, App(s, App(App(n,s),z)))))
  def suDefinition = """\n . \s . \z . (s, ( (n,s),z))"""
  // isZero   Lam(n, None, App(App(n,Lam(x, None, false)), true)
  def isZeroDefinition = """\n . ( (n, \ x . false), true) """
  //plus	Lam(a, None, Lam(b, None, Lam(c, None,Lam(d, None, App(App(a, c), App(App(b,c),d))))))
  def plusDefinition = """\a . \b . \c . \d . ( (a,c), ((b,c),d))"""
    
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