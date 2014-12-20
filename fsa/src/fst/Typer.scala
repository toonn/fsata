package fst

import Syntax._

/**
 * @author Sven Akkermans and Toon Nolten
 */
abstract class TypeException() extends Exception {
  def errorMessage: String;
  override def toString = errorMessage
}

case class UnequalTerms(t1: Term, t2: Term, names: Names) extends TypeException() {
  override def errorMessage = "Type mismatch: \n" + t1.prettyPrint(names) + " was not equal to " + t2.prettyPrint(names)
}
case class ExpectedPi(t: Term, ty: Term, names: Names) extends TypeException() {
  override def errorMessage = "Expected Pi type for " + t.prettyPrint(names) + ",\n instead got " + ty.prettyPrint(names)
}
case class ExpectedNat(t: Term, ty: Term, names: Names) extends TypeException() {
  override def errorMessage = "Expected Nat type for " + t.prettyPrint(names) + ",\n instead got " + ty.prettyPrint(names)
}
case class ExpectedBool(t: Term, ty: Term, names: Names) extends TypeException() {
  override def errorMessage = "Expected Bool type for " + t.prettyPrint(names) + ",\n instead got " + ty.prettyPrint(names)
}
case class ExpectedPair(t: Term, ty: Term, names: Names) extends TypeException() {
  override def errorMessage = "Expected Pair for " + t.prettyPrint(names) + ",\n it's type is " + ty.prettyPrint(names)
}
case class ExpectedSet(t: Term, ty: Term, names: Names) extends TypeException() {
  override def errorMessage = "Expected Set type for " + t.prettyPrint(names) + ",\n instead got " + ty.prettyPrint(names)
}
case class ExpectedSigma(t: Term, ty: Term, names: Names) extends TypeException() {
  override def errorMessage = "Expected Sigma type for " + t.prettyPrint(names) + ",\n instead got " + ty.prettyPrint(names)
}
case class RequiresAnnotation(t: Term, names: Names) extends TypeException() {
  override def errorMessage = "Term requires type annotation: \n" + t.prettyPrint(names)
}

class Typer(eval: Evaluator) {

  def shiftContext(ctx: Context, d: Int, c: Int): Context = ctx match {
    case List() => List()
    case (n, ty) :: ctx => (n, eval.shift(ty, d, c)) :: shiftContext(ctx, d, c + 1)
  }

  def lookupType(d: Int, ctx: Context): Term = {
    val t: Term = ctx(d)._2
    eval.shift(t, d + 1, 0)
  }

  def equalTerms(t1: Term, t2: Term, ctx: Context): Boolean = {
    val nctx = shiftContext(ctx, 1, 0)
    (eval.eval(t1), eval.eval(t2)) match {
      case (et1, et2) if et1 == et2 => true

      case (Lam(_, None, b1), Lam(_, None, b2))
      	if equalTerms(b1, b2, nctx) => true
      case (Lam(_, Some(ty1), b1), Lam(_, Some(ty2), b2))
      	if equalTerms(ty1, ty2, ctx) & equalTerms(b1, b2, nctx) => true

      case (Pi(_, ty1, ty2), Pi(_, ty3, ty4))
      	if equalTerms(ty1, ty3, ctx) & equalTerms(ty2, ty4, nctx) => true

      case (Pair(p1, p2), Pair(p3, p4))
      	if equalTerms(p1, p3, ctx) & equalTerms(p2, p4, ctx) => true
      case (Pair(p1, p2), Sigma(_, s1, s2))
      	if equalTerms(p1, s1, ctx) & equalTerms(p2, eval.shift(s2, -1, 0), ctx) => true
      case (Sigma(_, s1, s2), Pair(p1, p2))
      	if equalTerms(p1, s1, ctx) & equalTerms(p2, eval.shift(s2, -1, 0), ctx) => true
      case (Sigma(_, s1, s2), Sigma(_, s3, s4))
      	if equalTerms(s1, s3, ctx) & equalTerms(s2, s4, nctx) => true
      	
      // Let moet niet omdat het geen value is.
      
      case (et1, et2) => false
    }
  }

  def typeOf(t: Term, ctx: Context): Term = tcTerm(t, None, ctx)_2

  def tcTerm(t: Term, a: Option[Term], ctx: Context): (Term, Term) = {
    (t, a.map[Term](eval.eval)) match {

      case (Var(d), None) => {	
        (Var(d), lookupType(d, ctx))
      }
      
      case (Lam(name, None, t), Some(ty)) => {
    	  //println("" + Lam(n1, ty1, t) + " -l- " + ty)
    	  eval.eval(ty) match {
    	  	case Pi(n2, b, c) =>
    	  		 val (body, _) = tcTerm(t, Some(c), (name, b) :: ctx)
    	  		//println("" + Lam(n1, ty1, t) + " _l_ " + Pi(n2, b, c))
    	  		(Lam(name, Some(b), body), Pi(n2, b, c))
    	  	case ty1 => throw new ExpectedPi(ty, ty1, toNames(ctx))
    	  }
      }
      
//      case (Lam(name, ty1, t), Some(ty)) => {		//TODO Rereview
//    	  //println("" + Lam(n1, ty1, t) + " -l- " + ty)
//    	  eval.eval(ty) match {
//    	  	case Pi(n2, b, c) =>
//    	  		ty1 match {
//    	  			case None => val (body, _) = tcTerm(t, Some(c), (name, b) :: ctx)
//    	  						//println("" + Lam(n1, ty1, t) + " _l_ " + Pi(n2, b, c))
//    	  						(Lam(name, Some(b), body), Pi(n2, b, c))
//    	  			case Some(l_ty) => if (equalTerms(l_ty, b, ctx)) {
//    	  									val (body, _) = tcTerm(t, Some(c), (name, b) :: ctx)
//    	  									//println("" + Lam(n1, ty1, t) + " _l_ " + Pi(n2, b, c))
//    	  									(Lam(name, Some(b), body), Pi(n2, b, c))
//    	  								} else {
//    	  								  throw new UnequalTerms(l_ty, b, toNames((name, b) :: ctx))
//    	  								}
//    	  		}
//    	  	case ty1 => throw new ExpectedPi(ty, ty1, toNames(ctx))
//    	  }
//      }
      
      case (Lam(name, Some(a), t), None) => {
        //println("" + Lam(name, Some(a), t) + " -l- " + None)
        val (body, c) = tcTerm(t, None, (name, a) :: ctx)
        //println("" + Lam(name, Some(a), t) + " _l_ " + None)
        (Lam(name, Some(a), body), Pi(name, a, c))
      }
      
      case (App(f, t), None) => {
        /* Dit werkt nog niet, was een poging om inference op app sterker te maken.
        val (t1, t_ty) = tcTerm(t, None, ctx)
        eval.eval(f) match {
          case Lam(name, None, body) => {
            val (body1, body_ty) = tcTerm(eval.termSubstTop(t1, body), None, ctx)
            tcTerm(f, Some(Pi("_", t_ty, body_ty)), ctx)
            (App(f, t), body_ty)
          }
          case Lam(name, Some(t_ty), body) => {
            val (body1, body_ty) = tcTerm(eval.termSubstTop(t1, body), None, ctx)
            tcTerm(f, Some(Pi("_", t_ty, body_ty)), ctx)
            (App(f, t), body_ty)
          }
          case _ => throw new ExpectedPi(f, typeOf(f, ctx), toNames(ctx))
        }*/
        //println("App: " + f + " $ " + t)
        val (f1, ty1) = tcTerm(f, None, ctx)
        //println("f_ty: " + f1 + " : " + ty1)
        eval.eval(ty1) match {
          case Pi(name, a, b) => { 
            val (t1, _) = tcTerm(t, Some(a), ctx)
            (App(f1, t1), eval.termSubstTop(t1, b))
          }
          case _ => {
            throw new ExpectedPi(f, ty1, toNames(ctx))
          }
        }
      }
      
      case (Pi(name, a, b), None) => {
//        val uname = if (name == "_") { uniqueName(name, toNames(ctx)) } //TODO
//        			else { name }
        val (a1, _) = tcTerm(a, Some(Set), ctx) 
        val (b1, _) = tcTerm(b, Some(Set), (name, a1) :: ctx)
        (Pi(name, a1, b1), Set)
      }
      
      case (Set, None) => {
        (Set, Set)
      }
      case (Ann(a, t), None) => {
        tcTerm(t, Some(a), ctx)
      }
      //Nats
      case (Nat, None) => {
        (Nat, Set)
      }
      case (Zero, None) => {
        (Zero, Nat)
      }
      case (Succ(e), None) => {
        val (e1, ty1) = tcTerm(e, None, ctx)
        eval.eval(ty1) match {
          case Nat => {
            (Succ(e), Nat)
          }
          case _ => {
            throw new ExpectedNat(e, ty1, toNames(ctx))
          }
        }
      }
      case (Pred(e), None) => {
        val (e1, ty1) = tcTerm(e, None, ctx)
        eval.eval(ty1) match {
          case Nat => {
            (Pred(e), Nat)
          }
          case _ => {
            throw new ExpectedNat(e, ty1, toNames(ctx))
          }
        }
      }
      case (IsZero(e), None) => {
        val (e1, ty1) = tcTerm(e, None, ctx)
        eval.eval(ty1) match {
          case Nat => {
            (IsZero(e), Bool)
          }
          case _ => {
            throw new ExpectedNat(e, ty1, toNames(ctx))
          }
        }
      }
      
      //NatInd
      case (NatInd, None) => {
         //(P : Nat -> Set) -> P 0 -> ((n : Nat) -> P n -> P (succ n)) -> (n : Nat) -> P n
    	  (NatInd, Pi("P", Pi("_", Nat, Set),
    	               Pi("_", App(Var(0), Zero),
    	                   Pi("_", Pi("n", Nat,
    	                		   	   Pi("_", App(Var(2), Var(0)),
    	                		   		   App(Var(3), Succ(Var(1))))),
    	                       Pi("n", Nat,
    	                           App(Var(3), Var(0)))))))
      }
      
      //Bools
      case (Bool, None) => {
        (Bool, Set)
      }
      case (True, None) => {
        (True, Bool)
      }
      case (False, None) => {
        (False, Bool)
      }
      case (IfThenElse(c, e1, e2), None) => {
        val (c1, ty1) = tcTerm(c, None, ctx)
        val (e11, ty11) = tcTerm(e1, None, ctx)
        val (c21, ty21) = tcTerm(e2, None, ctx)
        eval.eval(ty1) match {
          case Bool => {
            if (eval.eval(ty1).equals(True)) {
              (IfThenElse(c1, e1, e2), ty11)
            } else {
              (IfThenElse(c1, e1, e2), ty21)
            }
          }
          case _ => {
            throw new ExpectedBool(c1, ty1, toNames(ctx))
          }
        }
      }
      //Sigma types
      case (Sigma(v, a, b), None) => {
        val (a1, _) = tcTerm(a, Some(Set), ctx)
        val (b1, _) = tcTerm(b, Some(Set), (v, a1) :: ctx)
        (Sigma(v, a1, b1), Set)
      }
      case (Pair(s, t), Some(Sigma(v, a , b))) => {
        val (s1, s_ty) = tcTerm(s, Some(a), ctx)
        val (t1, t_ty) = tcTerm(t, Some(eval.termSubstTop(s1, b)), ctx)
        (Pair(s1, t1), Sigma(v, s_ty, t_ty))
      }
      case (Pair(s, t), None) => {
        val (s1, s_ty) = tcTerm(s, None, ctx)
        val (t1, t_ty) = tcTerm(t, None, ctx)
        (Pair(s1, t1), Sigma("_", s_ty, t_ty))
      }
      case (First(t), None) => {
        tcTerm(t, None, ctx) match {
          case (_, Sigma(_, a, _)) => (First(t), a)
          case (_, ty) => throw new ExpectedPair(t, ty, toNames(ctx))
        }
      }
      case (Second(t), None) => {
        tcTerm(t, None, ctx) match {
          case (_, Sigma(v, a, b)) => (Second(t), eval.termSubstTop(First(t), b))
          case (_, ty) => throw new ExpectedPair(t, ty, toNames(ctx))
        }
      }
      
      /*case (Let(name: String, ty: Term, term: Term, body: Term), Some(a)) => {
        val (ty1, Set) = tcTerm(ty, Some(Set), ctx)
        val (term1, term_ty) = tcTerm(term, Some(ty1), ctx)
        val (body1, body_ty) = tcTerm(eval.termSubstTop(term1, body), Some(a), ctx)
        (Let(name, ty1, term1, body1), body_ty)
      }*/

      case (t, Some(a)) => {
        //println("\n" + t + " -- " + a)
        val (tt: Term, at) = tcTerm(t, None, ctx)
        val (t1: Term, a1) = (eval.eval(tt), eval.eval(at))
        //println("\n" + t1 + " __ " + a1)
        if (!equalTerms(a, a1, ctx)) {
          throw new UnequalTerms(t, t1, toNames(ctx))
        }
        (t1, a1)
      }


      //Bools
      case (TUnit, None) => {
        (TUnit, Set)
      }
      case (Unit, None) => {
        (Unit, TUnit)
      }
      //Let expression
      case (Let(name: String, ty: Term, term: Term, body: Term), None) => {
        val (ty1, Set) = tcTerm(ty, Some(Set), ctx)
        val (term1, term_ty) = tcTerm(term, Some(ty1), ctx)
        val (body1, body_ty) = tcTerm(eval.termSubstTop(term1, body), None, ctx)
        (Let(name, ty1, term1, body1), body_ty)
      }
      //TArr
      case (TArr(t1: Term, t2: Term), None) => {
        val (tt1, tty1) = tcTerm(t1, None, ctx)
        val (tt2, tty2) = tcTerm(t2, None, ctx)
        (TArr(t1, t2), Set)
      }

      //Identity types
      case (I, None) => {
       // (A : Set) -> A -> A -> Set
        (I, Pi("A", Set,
        		Pi("_", Var(0),
        		    Pi("_", Var(1),
        		        Set))))
            
      }
      case (Refl, None) => {
        // (A : Set) -> (x : A) -> I A x x
        (Refl, Pi("A", Set,
        		   Pi("x", Var(0),
        			   App(App(App(I, Var(1)), Var(0)), Var(0)))))
      }
      case (Subst, None) => {
       //(A : Set) -> (x : A) -> (y : A) -> (P : A -> Set) -> I A x y -> P x -> P y
        (Subst, Pi("A", Set,
        			Pi("x", Var(0),
        			    Pi("y", Var(1),
        			        Pi("P", Pi("_", Var(2),
        			        			Set),
        			            Pi("_", App(App(App(I,Var(3)),Var(2)),Var(1)),
        			            	Pi("_", App(Var(1),Var(3)),
        			            	    App(Var(2), Var(3)))))))))
        			            	    
        			         
      }
      
      //BoolElim
      case (BoolElim, None) => {
        //(P : Bool -> Set) -> P true -> P false -> (b : Bool)-> P b        
        (BoolElim, Pi("P", Pi("_", Bool, Set),
        			   Pi("_", App(Var(0), True),
        			       Pi("_", App(Var(1), False),
        					   Pi("x", Bool,
        					       App(Var(3),Var(0)))))))
      }

      case (t, None) => throw new RequiresAnnotation(t, toNames(ctx))
    }
  }
}