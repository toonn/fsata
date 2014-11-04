package fst

/**
 * 
 * @author VUL IN AUB.
 */

import Syntax._

abstract class TypeException() extends Exception {
  def errorMessage : String;
  override def toString = errorMessage
}

case class UnequalTerms(t1: Term,t2: Term, names: Names) extends TypeException() {
  override def errorMessage = "Type mismatch: \n" + t1.prettyPrint(names) + " was not equal to " + t2.prettyPrint(names)
}
case class ExpectedPi(t: Term, ty: Term, names: Names) extends TypeException() {
  override def errorMessage = "Expected Pi type for " + t.prettyPrint(names) + ",\n instead got " + ty.prettyPrint(names)
}
case class ExpectedSigma(t: Term, ty: Term, names: Names) extends TypeException() {
  override def errorMessage = "Expected Sigma type for " + t.prettyPrint(names) + ",\n instead got " + ty.prettyPrint(names)
}
case class RequiresAnnotation(t: Term, names: Names) extends TypeException() {
  override def errorMessage = "Term requires type annotation: \n" + t.prettyPrint(names)
}

class Typer(eval: Evaluator) {
  
  def shiftContext(ctx: Context,d: Int, c: Int) : Context = ctx match {
    case List()   => List()
    case (n,ty) :: ctx => (n,eval.shift(ty,d,c)) :: shiftContext(ctx,d,c+1)
  }
  
  def lookupType(d: Int,ctx: Context): Term = {
	val t : Term = ctx(d)._2
	eval.shift(t,d+1,0)
  }
  
  def equalTerms(t1: Term, t2: Term, ctx: Context): Boolean = {
    (eval.eval(t1),eval.eval(t2)) match {
      case (t1,t2) if t1 == t2 => true
      // TODO: add more cases here
      case (t1,t2) => false
    }      
  }
  
  def typeOf(t: Term, ctx: Context): Term = tcTerm(t,None,ctx)_2
  
  def tcTerm(t: Term, a: Option[Term], ctx: Context): (Term,Term) = {
    (t,a.map[Term](eval.eval)) match {
    case (Var(d),None) => {
      (Var(d),lookupType(d,ctx))
    }
    case (Lam(n1,None,t),Some(Pi(n2,b,c))) => {
      val (body, _) = tcTerm(t,Some(c),(n1,b)::ctx)
      (Lam(n1,Some(b),body),Pi(n2,b,c))
    }
    case (Lam(name,Some(a),t),None) => {
      val (body, c) = tcTerm(t,None,(name,a)::ctx)
      (Lam(name, Some(a),body),Pi(name,a,c))
    }
    case (App(f,t),None) => {
      val (f1, ty1) = tcTerm(f,None,ctx)
      eval.eval(ty1) match {
        case Pi(name,a,b) => {
          val (t1, _) = tcTerm(t,Some(a),ctx)
          (App(f1,t1), eval.termSubstTop(t1,b))
        } 
        case _       => {
          throw new ExpectedPi(f,ty1,toNames(ctx)) //TODO
        }
      }
    }
    case (Pi(name,a,b),None) => {
      val (a1, _) = tcTerm(a,Some(Set),ctx)
      val (b1, _) = tcTerm(b,Some(Set),(name,a1)::ctx)
      (Pi(name,a1,b1),Set)
    }
    case (Set,None) => {
      (Set,Set)
    }
    case (Ann(a,t),None) => tcTerm(t,Some(a),ctx)
    case (t,Some(a)) => {
      val (t1:Term, a1) = tcTerm(t,None,ctx)
      if (!equalTerms(a,a1,ctx)) throw new UnequalTerms(a,a1,toNames(ctx))
      (t1,a1)
    }
    case (t,None) => throw new RequiresAnnotation(t,toNames(ctx))
    }
  }
}