package fst

/**
 *
 * @author Akkermans Sven and Nolten Toon
 */

import Syntax._

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
//SAN: added
case class ExpectedNat(t: Term, ty: Term, names: Names) extends TypeException() {
  override def errorMessage = "Expected Nat type for " + t.prettyPrint(names) + ",\n instead got " + ty.prettyPrint(names)
}
//SAN: added
case class ExpectedBool(t: Term, ty: Term, names: Names) extends TypeException() {
  override def errorMessage = "Expected Bool type for " + t.prettyPrint(names) + ",\n instead got " + ty.prettyPrint(names)
}
//SAN: Added
case class ExpectedPair(t: Term, ty: Term, names: Names) extends TypeException() {
  override def errorMessage = "Expected Pair for " + t.prettyPrint(names) + ",\n it's type is " + ty.prettyPrint(names)
}
//SAN: Added
case class ExpectedSet(t: Term, ty: Term, names: Names) extends TypeException() {
  override def errorMessage = "Expected Set type for " + t.prettyPrint(names) + ",\n instead got " + ty.prettyPrint(names)
}

case class ExpectedSigma(t: Term, ty: Term, names: Names) extends TypeException() {
  override def errorMessage = "Expected Sigma type for " + t.prettyPrint(names) + ",\n instead got " + ty.prettyPrint(names)
}
case class RequiresAnnotation(t: Term, names: Names) extends TypeException() {
  override def errorMessage = "Term requires type annotation: \n" + t.prettyPrint(names)
}

/**
 * Sven's Additional Notes (SAN):
 *
 * Types of the variables in the context are allowed to depend on the values of the variables before it.
 */
class Typer(eval: Evaluator) {

  def shiftContext(ctx: Context, d: Int, c: Int): Context = ctx match {
    case List() => List()
    case (n, ty) :: ctx => (n, eval.shift(ty, d, c)) :: shiftContext(ctx, d, c + 1)
  }

  def lookupType(d: Int, ctx: Context): Term = {
    val t: Term = ctx(d)._2
    eval.shift(t, d + 1, 0)
  }

  //SAN: This function is incomplete and just checks if two terms have the same syntax.
  //	Add an evaluator to the language and use it in the implementation of this function.
  def equalTerms(t1: Term, t2: Term, ctx: Context): Boolean = {
    val nctx = shiftContext(ctx, 1, 0)
    (eval.eval(t1), eval.eval(t2)) match {
      case (et1, et2) if et1 == et2 => true
      // TODO: add more cases here
      //SAN Addition
      case (Lam(_, None, t1), Lam(_, None, t2)) if equalTerms(t1, t2, nctx) => true
      case (Lam(_, Some(ty1), t1), Lam(_, Some(ty2), t2)) if equalTerms(ty1, ty2, nctx) & equalTerms(t1, t2, nctx) => true

      case (Pi(_, ty1, ty2), Pi(_, ty3, ty4)) if equalTerms(ty1, ty3, nctx) & equalTerms(ty2, ty4, nctx) => true

      case (et1, et2) => false
    }
  }

  def typeOf(t: Term, ctx: Context): Term = tcTerm(t, None, ctx)_2

  /**
   * Sven's Additional Notes (SAN):
   *
   * Bi-directional typechecking algorithm
   * Note that we have to give a directed version of each of the rules of Figure 3 on paper/latex.
   * Note that there should be a rule to switch from checking mode to inference mode when necessary.
   *
   */
  //SAN:		If a is None, the typechecker is in inference mode.
  def tcTerm(t: Term, a: Option[Term], ctx: Context): (Term, Term) = {
    (t, a.map[Term](eval.eval)) match {
      // SAN: Type checking for variable.
      case (Var(d), None) => {
        (Var(d), lookupType(d, ctx))
      }
      // SAN: Type checking for abstraction (lambda expression) unannoted version (I think)
      //		Has to check that argument type is of type Set    
      case (Lam(n1, ty1, t), Some(ty)) => {
    	  println("" + Lam(n1, ty1, t) + " -l- " + ty)
    	  eval.eval(ty) match {
    	  	case Pi(n2, b, c) =>
    	  		ty1 match {
    	  			case None => val (body, _) = tcTerm(t, Some(c), (n1, b) :: ctx)
    	  						println("" + Lam(n1, ty1, t) + " _l_ " + Pi(n2, b, c))
    	  						(Lam(n1, Some(b), body), Pi(n2, b, c))
    	  			case Some(l_ty) => if (equalTerms(l_ty, b, ctx)) {
    	  									val (body, _) = tcTerm(t, Some(c), (n1, b) :: ctx)
    	  									println("" + Lam(n1, ty1, t) + " _l_ " + Pi(n2, b, c))
    	  									(Lam(n1, Some(b), body), Pi(n2, b, c))
    	  								} else {
    	  								  throw new UnequalTerms(l_ty, b, toNames((n1, b) :: ctx))
    	  								}
    	  		}
    	  	case ty1 => throw new ExpectedPi(ty, ty1, toNames(ctx)) //TODO
    	  }
      }
      // SAN: Type checking for abstraction (lambda expression) annoted version
      //		Has to check that argument type is of type Set
      case (Lam(name, Some(a), t), None) => {
        println("" + Lam(name, Some(a), t) + " -l- " + None)
        val (body, c) = tcTerm(t, None, (name, a) :: ctx)
        println("" + Lam(name, Some(a), t) + " _l_ " + None)
        (Lam(name, Some(a), body), Pi(name, a, c))
      }
      // SAN: Type checking for application
      case (App(f, t), None) => {
        //println("App: " + f + " $ " + t)
        val (f1, ty1) = tcTerm(f, None, ctx) //SAN: type of f, ty1, shoud be equal to Pi type (name, a,b).
        //println("f_ty: " + f1 + " : " + ty1)
        eval.eval(ty1) match {
          case Pi(name, a, b) => { //SAN: in that case, arg of t should be type a and app f t has type the value of the Pi type
            val (t1, _) = tcTerm(t, Some(a), ctx) //		for the argument the function was applied to
            (App(f1, t1), eval.termSubstTop(t1, b))
          }
          case _ => {
            throw new ExpectedPi(f, ty1, toNames(ctx)) //TODO
          }
        }
      }
      // SAN: Type checking for dependent function
      case (Pi(name, a, b), None) => {
//        val uname = if (name == "_") { uniqueName(name, toNames(ctx)) }
//        			else { name }
        val (a1, _) = tcTerm(a, Some(Set), ctx) //SAN: a1 has to be a type
        val (b1, _) = tcTerm(b, Some(Set), (name, a1) :: ctx) //SAN: b1 has to be a type with (x:a1) added to the context
        (Pi(name, a1, b1), Set)
      }
      // SAN: Type checking for Set
      case (Set, None) => {
        (Set, Set)
      }
      case (Ann(a, t), None) => {
        tcTerm(t, Some(a), ctx)
      }
      case (t, Some(a)) => {
        println("\n" + t + " -- " + a)
        val (t1: Term, a1) = tcTerm(t, None, ctx)
        println("\n" +t1 + " __ " + a1)
        if (!equalTerms(a, a1, ctx)) {
          throw new UnequalTerms(t, t1, toNames(ctx))
        }
        (t1, a1)
      }

      ////////////////////////////////////////
      //SAN  Additions: underneath this line//
      ////////////////////////////////////////
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
      //NatInd : SAN Incomplete, I think
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
      //SAN: Sigma types
      //TODO: Some mistakes here, tricky
      case (Sigma(v, a, b), None) => {
        val (a1, _) = tcTerm(a, Some(Set), ctx)
        val (b1, _) = tcTerm(b, Some(Set), (v, a1) :: ctx)
        (Sigma(v, a1, b1), Set)
      }
      case (Pair(s, t), None) => {
        val (s1, s_ty) = tcTerm(s, None, ctx)
        val (t1, t_ty) = tcTerm(t, None, ctx)
        (Pair(s1, t1), Sigma("x", s_ty, t_ty))
      }
      case (First(t), None) => {
        tcTerm(t, None, ctx) match {
          case (Pair(t1, t2), ty) =>
          	eval.eval(ty) match {
          		case Sigma(v, a, b) => (t1, a)
          		case _ => throw new ExpectedSigma(Pair(t1, t2), ty, toNames(ctx))
          	}
          case (tnopair, tynopair) => throw new ExpectedPair(t, tynopair, toNames(ctx))
        }
      }
      case (Second(t), None) => {
        val (Pair(t1, t2), ty) = tcTerm(t, None, ctx)
        eval.eval(ty) match {
          case Sigma(v, a, b) => (t2, eval.termSubstTop(a, b))
          case _ => throw new ExpectedSigma(Pair(t1, t2), ty, toNames(ctx))
        }
      }
      //SAN: Bools
      case (TUnit, None) => {
        (TUnit, Set)
      }
      case (Unit, None) => {
        (Unit, TUnit)
      }
      //SAN: Let expression (*INCOMPLETE*)
      case (Let(name: String, ty: Term, term: Term, body: Term), None) => {
        val (ty1, Set) = tcTerm(ty, Some(Set), ctx)
        val (term1, term_ty) = tcTerm(term, Some(ty1), ctx)
        val (body1, body_ty) = tcTerm(eval.termSubstTop(term1, body), None, ctx)
        println("\nty1: " + ty1)
        println("\nterm1: " + term1)
        println("\nbody: " + body)
        println("\nbody1: " + body1)
        (Let(name, ty1, term1, body1), body_ty)
      }
      //SAN: TArr, (*INCOMPLETE*)
      case (TArr(t1: Term, t2: Term), None) => {
        val (tt1, tty1) = tcTerm(t1, None, ctx)
        val (tt2, tty2) = tcTerm(t2, None, ctx)
        (TArr(t1, t2), Set)
      }

      //SAN: Identity types (*INCOMPLETE*)
      case (I, None) => {
       // (A : Set) -> A -> A -> Set
        (I, Pi("A",
        		Set,
        		Pi("_",
        		    Var(1),
        		    Pi("_",
        		        Var(2),
        		        Set))))
            
      }
      case (Refl, None) => {
        // (A : Set) -> (x : A) -> I A x x
        (Refl, Pi("A",
        			Set,
        			Pi("x",
        			    Var(0),
        			    Pi("_",
        			        Pi("_", I, Var(2)),
        			        App(Var(0),Var(0))))))
      }
      case (Subst, None) => {
       //(A : Set)->(x : A) ->(y : A) ->(P : A ->Set) ->I A x y ->P x ->P y
        (Subst, Pi("A",
        			Set,
        			Pi("x",
        			    Var(0),
        			    Pi("y",
        			        Var(1),
        			        Pi("P",
        			            Pi("_",Var(3),Set),
        			            Pi("_", 
        			            	App(App(App(I,Var(4)),Var(3)),Var(2)),
        			            	Pi("_",
        			            	    App(Var(2),Var(4)),
        			            	    Pi("_",Var(3),Var(4)))))))))
        			            	    
        			         
      }
      
      //SAN: BoolElim (*INCOMPLETE*)
      case (BoolElim, None) => {
        //(P : Bool -> Set) -> P true -> P false -> (b : Bool)-> P b        
        (BoolElim, Pi("P", Pi("_", Bool, Set),
        			   Pi("_", App(Var(0), True),
        			       Pi("_", App(Var(1), False),
        					   Pi("x", Bool,
        					       App(Var(3),Var(0)))))))
      }

      //End of SAN additions
      case (t, None) => throw new RequiresAnnotation(t, toNames(ctx))
    }
  }
}