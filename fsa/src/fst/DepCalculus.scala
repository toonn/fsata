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
  override def mkAbs(v: String, ty: Option[Term], t: Term) =
  	ty match {
  		case None => Lam(v, None, t)
  		case Some(ty1) => Lam(v,Some(ty1),t)
  	}
  override def mkApp(f : Term, a : Term) = App(f,a)
  
  override def mkLet(v: String, ty: Term, vi: Term, t: Term) : Term = Let(v,ty,vi,t)

  	//SAN: I think this ( t1 -> t2 ), unsure. 
  override def mkTArr(t1 : Term, t2: Term) = mkPi("_",t1,eval.shift(t2,1,0))
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
  override def mkSucc(e: Term) = Succ(e)
  override def mkPred(e: Term) = Pred(e)
  override def mkIsZero(e: Term) = IsZero(e)
  override def mkNatInd = NatInd
  
  // unit type
  override def mkTUnit = TUnit
  override def mkUnit = Unit
  
  // sigma types
  override def mkSigma(v: String, a: Term, b: Term) : Term = Sigma(v,a,b)
  override def mkPair(x: Term, y: Term) : Term = Pair(x,y)
  override def mkFirst(t: Term) : Term = First(t)
  override def mkSecond(t: Term) : Term = Second(t)
    
  // singleton types //SAN: Optional
  override def mkI = I
  override def mkRefl = Refl
  override def mkSubst = Subst
  
  // dependent if //SAN: Optional
  override def mkBoolElim = notImplemented
  
  
  //SAN: Added a couple of possible solution templates but I'm unsure of the correct implementation in Scala. No examples...
  //	Hence, I'll do only some because I would want to test them first.
  
  def churchBoolDefinition =  """(A : Set) -> A -> A  -> A"""
    
    // true Lam(t, None, Lam(f, None, t))
  def truDefinition = """\A . \x . \y . x"""
    // fls Lam(t, None, Lam(f, None, f))
  def flsDefinition = """\A . \x . \y . y"""
    // not Lam(a, None, Lam(t, None, Lam(f, None, App( App(a,f), t))))
  def notDefinition = """ \a . \A . \t . \f . a A f t"""
    // and Lam(a, None, Lam(b, None, App(App(a,b), a))))
  def andDefinition = """\a . \b . \A . a ((_ : A) -> (_ : A) -> A) (b A) (a A)"""
    // or Lam(a, None, Lam(b, None, App( App(a, a), None, b))))
  def orDefinition = """\a . \b . \A . a ((_ : A) -> (_ : A) -> A) (a A) (b A)"""
    
  def boolEqDefinition = """\b1 . \b2 . b1 (b2 tru fls) (b2 fls tru)"""
    
    
  // TODO  
  def churchNatDefinition = """(A : Set) -> A -> (A -> A) -> A"""
    
  // Zero Lam(n, None, Lam (s, None, s)
  def zeDefinition = """\A .\z . \s . z"""
  // Succ	Lam( n, None, Lam(s, None, Lam (z, None, App(s, App(App(n,s),z)))))
  def suDefinition = """\n . \A . \z . \s . s (n A z s)"""
  // isZero   Lam(n, None, App(App(n,Lam(x, None, false)), true)
  def isZeroDefinition = """\n . n tru (\x . fls)"""
  //plus	Lam(a, None, Lam(b, None, Lam(c, None,Lam(d, None, App(App(a, c), App(App(b,c),d))))))
  def plusDefinition = """ \a . \b . \A . \z . \s . a (b z s) s"""
    
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