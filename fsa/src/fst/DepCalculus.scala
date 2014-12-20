package fst

import Syntax._

/**
 * This is the solution template for your dependently typed calculus.
 *
 * @author Sven Akkermans and Toon Nolten
 */
class DepCalculus extends Calculus[Term, Term, Unit] {

  type Term = Syntax.Term

  val parser = new DepParser(this);
  val eval = new Evaluator();

  // essentials
  override def mkVar(i : Int) = Var(i)
  override def mkAbs(v : String, ty : Option[Term], t : Term) = Lam(v, ty, t)
  override def mkApp(f : Term, a : Term) = App(f, a)

  override def mkLet(v : String, ty : Term, vi : Term, t : Term) : Term = Let(v, ty, vi, t)

  override def mkTArr(t1 : Term, t2 : Term) = mkPi("_", t1, eval.shift(t2, 1, 0))
  override def mkPi(v : String, t1 : Term, t2 : Term) = Pi(v, t1, t2)
  override def mkSet = Set

  override def mkAnnot(ty : Term, t : Term) = Ann(ty, t)

  // booleans
  override def mkBool = Bool
  override def mkTrue = True
  override def mkFalse = False
  override def mkIfThenElse(c : Term, e1 : Term, e2 : Term) = IfThenElse(c, e1, e2)

  // naturals
  override def mkNat = Nat
  override def mkZero = Zero
  override def mkSucc(e : Term) = Succ(e)
  override def mkPred(e : Term) = Pred(e)
  override def mkIsZero(e : Term) = IsZero(e)
  override def mkNatInd = NatInd

  // unit type
  override def mkTUnit = TUnit
  override def mkUnit = Unit

  // sigma types
  override def mkSigma(v : String, a : Term, b : Term) : Term = Sigma(v, a, b)
  override def mkPair(x : Term, y : Term) : Term = Pair(x, y)
  override def mkFirst(t : Term) : Term = First(t)
  override def mkSecond(t : Term) : Term = Second(t)

  // singleton types
  override def mkI = I
  override def mkRefl = Refl
  override def mkSubst = Subst

  // dependent if
  override def mkBoolElim = BoolElim

  //church booleans
  def churchBoolDefinition = """(A : Set) -> A -> A -> A"""

  def truDefinition = """\A . \x . \y . x"""
  def flsDefinition = """\A . \x . \y . y"""
  def notDefinition = """ \a . \A . \t . \f . a A f t"""
  def andDefinition = """\a . \b . \A . a (A -> A -> A) (b A) (a A)"""
  def orDefinition = """\a . \b . \A . a (A -> A -> A) (a A) (b A)"""
  def boolEqDefinition = """\b1 . \b2 . \A . b1
  								(A -> A -> A)
    							(b2 (A -> A -> A)
    								((b1) A)
    								((b2) A))
  								(b2 (A -> A -> A)
  									((b1) A)
  									((\x . \y . x)))"""

  // church numerals  
  def churchNatDefinition = """(A : Set) -> A -> (A -> A) -> A"""

  def zeDefinition = """\A .\z . \s . z"""
  def suDefinition = """\n . \A . \z . \s . s (n A z s)"""
  def isZeroDefinition = """\n . n bool tru (\_ . fls)""" // This assumes bool, tru and fls are defined in a let beforehand, allowed, see forum.
  def plusDefinition = """\a . \b . a nat (b nat ze su) su""" // This assumes nat, ze and su are defined in a let beforehand, allowed, see forum.

  //usage of natind  
  def timesDefinition = """natInd (\n: Nat . Nat -> Nat) (\_ : Nat . 0) 
    								(\n : Nat . \h : Nat -> Nat . \v: Nat . plus (h v) v)"""
  def pred2Definition = """natInd (\n: Nat . Nat) (0)
    								(\n : Nat . \h : Nat . n)"""

  //optional proof theorem 1,  right zero for +  
  def proofTerm = """natInd (\n : Nat . I Nat (plus n 0) n)
    						(refl Nat 0)
    						(\n : Nat . \hyp : I Nat (plus n 0) n .
    							subst Nat (plus n 0) n
    								(\t : Nat . I Nat (succ (plus n 0)) (succ t)) (hyp)
    								(refl Nat (succ (plus n 0))))"""
  //usage of boolelim
  def ifXThenNatElseBoolDefinition = """boolElim (\n: Bool . if n then Nat else Bool) 0 true"""
}