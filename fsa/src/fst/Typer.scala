package fst

/**
 * 
 * @author Akkermans Sven and Nolten Toon
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
  override def errorMessage = "Expected Pair type for " + t.prettyPrint(names) + ",\n instead got " + ty.prettyPrint(names)
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
  
  def shiftContext(ctx: Context,d: Int, c: Int) : Context = ctx match {
    case List()   => List()
    case (n,ty) :: ctx => (n,eval.shift(ty,d,c)) :: shiftContext(ctx,d,c+1)
  }
  
  def lookupType(d: Int,ctx: Context): Term = {
	val t : Term = ctx(d)._2
	eval.shift(t,d+1,0)
  }
  
  //SAN: This function is incomplete and just checks if two terms have the same syntax.
  //	Add an evaluator to the language and use it in the implementation of this function.
  def equalTerms(t1: Term, t2: Term, ctx: Context): Boolean = {
    (eval.eval(t1),eval.eval(t2)) match {
      case (t1,t2) if t1 == t2 => true
      // TODO: add more cases here
      case (t1,t2) => false
    }      
  }
  
  def typeOf(t: Term, ctx: Context): Term = tcTerm(t,None,ctx)_2
  
  /**
   * Sven's Additional Notes (SAN):
   * 
   * Bi-directional typechecking algorithm
   * Note that we have to give a directed version of each of the rules of Figure 3 on paper/latex.
   * Note that there should be a rule to switch from checking mode to inference mode when necessary.
   * 
   */
  //SAN:		If a is None, the typechecker is in inference mode.
  def tcTerm(t: Term, a: Option[Term], ctx: Context): (Term,Term) = {
    (t,a.map[Term](eval.eval)) match {
    	// SAN: Type checking for variable.
    case (Var(d),None) => {
      (Var(d),lookupType(d,ctx))
    }
    	// SAN: Type checking for abstraction (lambda expression) unannoted version (I think)
    	//		Has to check that argument type is of type Set    
    case (Lam(n1,None,t),Some(Pi(n2,b,c))) => {
      val (body, _) = tcTerm(t,Some(c),(n1,b)::ctx)
      (Lam(n1,Some(b),body),Pi(n2,b,c))
    }
        // SAN: Type checking for abstraction (lambda expression) annoted version
    	//		Has to check that argument type is of type Set
    case (Lam(name,Some(a),t),None) => {
      val (body, c) = tcTerm(t,None,(name,a)::ctx)
      (Lam(name, Some(a),body),Pi(name,a,c))
    }
    	// SAN: Type checking for application
    case (App(f,t),None) => {
      val (f1, ty1) = tcTerm(f,None,ctx)	//SAN: type of f, ty1, shoud be equal to Pi type (name, a,b).
      eval.eval(ty1) match {
        case Pi(name,a,b) => {					//SAN: in that case, arg of t should be type a and app f t has type the value of the Pi type
          val (t1, _) = tcTerm(t,Some(a),ctx)	//		for the argument the function was applied to
          (App(f1,t1), eval.termSubstTop(t1,b))
        } 
        case _       => {
          throw new ExpectedPi(f,ty1,toNames(ctx)) //TODO
        }
      }
    }
    	// SAN: Type checking for dependent function
    case (Pi(name,a,b),None) => {
      val (a1, _) = tcTerm(a,Some(Set),ctx) //SAN: a1 has to be a type
      val (b1, _) = tcTerm(b,Some(Set),(name,a1)::ctx) //SAN: b1 has to be a type with (x:a1) added to the context
      (Pi(name,a1,b1),Set)
    }
    	// SAN: Type checking for Set
    case (Set,None) => {
      (Set,Set)
    }
    case (Ann(a,t),None) => {
      tcTerm(t,Some(a),ctx)
    }
    case (t,Some(a)) => {
      val (t1:Term, a1) = tcTerm(t,None,ctx)
      if (!equalTerms(a,a1,ctx)) throw new UnequalTerms(a,a1,toNames(ctx))
      (t1,a1)
    }
    
    ////////////////////////////////////////
    //SAN  Additions: underneath this line//
    ////////////////////////////////////////
    	//Nats
    case(Nat, None) => {
      (Nat,Set)
    }
    case(Zero, None) => {
      (Zero,Nat)
    }
    case(Succ(e), None) => {
    	val (e1,ty1) = tcTerm(e,None,ctx)
    	eval.eval(ty1) match {
        case Nat => {
           (Succ(e),Nat)
        }
        case _       => {
          throw new ExpectedNat(e,ty1,toNames(ctx)) //TODO
        }
    	}
    }
    case(Pred(e), None) => {
    	val (e1,ty1) = tcTerm(e,None,ctx)
    	eval.eval(ty1) match {
        case Nat => {
           (Pred(e),Nat)
        }
        case _       => {
          throw new ExpectedNat(e,ty1,toNames(ctx))
        }
    	}
    }
    case(IsZero(e), None) => {
    	val (e1,ty1) = tcTerm(e,None,ctx)
    	eval.eval(ty1) match {
        case Nat => {
           (IsZero(e),Bool)
        }
        case _       => {
          throw new ExpectedNat(e,ty1,toNames(ctx))
        }
    	}
    }
    case(NatInd, None) => {
      (NatInd,Nat)
    }
    	//Bools
    case(Bool, None) => {
      (Bool,Set)
    }
    case(True, None) => {
      (True,Bool)
    }
    case(False, None) => {
      (False,Bool)
    }
    case(IfThenElse(c,e1,e2), None) => {
    	val (c1,ty1) = tcTerm(c,None,ctx)
    	val (e11,ty11) = tcTerm(e1,None,ctx)
    	val (c21,ty21) = tcTerm(e2,None,ctx)
    	eval.eval(ty1) match {
        case Bool => {
          if( eval.eval(ty1).equals(True)) {
            (IfThenElse(c1,e1,e2),ty11)
          } else {
            (IfThenElse(c1,e1,e2),ty21)
          }
        }
        case _       => {
          throw new ExpectedBool(c1,ty1,toNames(ctx))
        }
    	}    
    }
    	//SAN: Sigma types
    		//TODO: Some mistakes here, tricky
    case(Sigma(v,a,b), None) => {
      val (a1, _) = tcTerm(a,Some(Set),ctx) 
      val (b1, _) = tcTerm(b,Some(Set),(v,a1)::ctx)
      (Sigma(v,a1,b1),Set)
    }
    case(Pair(s,t), None) => {
      val (s1, _) = tcTerm(s,Some(Set),ctx) 
      val (t1, _) = tcTerm(t,Some(Set),ctx)
      (Pair(s1,t1),Set)
    }
    case(First(t), None) => {
       val (t1, ty1) = tcTerm(t,Some(Set),ctx)
       eval.eval(ty1) match {
        case Pair(_,_) => {
          (First(t), ty1)
        }
        case _       => {
          throw new ExpectedPair(t1,ty1,toNames(ctx))
        }
       }
    }
    case(Second(t), None) => {
       val (t1, ty1) = tcTerm(t,Some(Set),ctx)
       eval.eval(ty1) match {
        case Pair(_,_) => {
          (Second(t), ty1)
        }
        case _       => {
          throw new ExpectedPair(t1,ty1,toNames(ctx))
        }
       }
    }
    	//SAN: Bools
    case(TUnit, None) => {
      (TUnit,Set)
    }
    case(Unit, None) => {
      (Unit,TUnit)
    }
        //SAN: Let expression (*INCOMPLETE*)
    case(Let(v: String, ty: Term, vi: Term, t: Term), None) => {
    	val (ty1,ty_ty) = tcTerm(ty,None,ctx)
    	val (vi1,vi_ty) = tcTerm(vi,None,ctx)
    	val (t1,t_ty) = tcTerm(t,None,ctx)
    	eval.eval(ty_ty) match {
        case Set => {
          if(eval.eval(vi_ty).equals(ty_ty)) {
            (Let(v,ty_ty,vi_ty,t_ty), Set)
          } else {
        	  throw new UnequalTerms(ty_ty,vi_ty,toNames(ctx))          
          }
        }
        case _       => {
          throw new ExpectedSet(ty,ty_ty,toNames(ctx))
        }
    	}    
    }
    	//SAN: TArr, (*INCOMPLETE*)
    case(TArr(t1 : Term, t2 : Term), None) => {
        val (tt1,tty1) = tcTerm(t1,None,ctx)
    	val (tt2,tty2) = tcTerm(t2,None,ctx)
    	(TArr(t1,t2),Set)
    }
    
    //End of SAN additions
    case (t,None) => throw new RequiresAnnotation(t,toNames(ctx))
    }
  }
}