package fst

import Syntax._
import java.util.NoSuchElementException

class Evaluator {
	
	//SAN TODO (*INCOMPLETE*)
	//	we could skip the terms that don't have anything to shift.
	def shift(t:Term, d:Int, c:Int): Term = t match {

	  case Var(i) => if (i<c) Var(i) else Var(i+d)
	  
	  //SAN: Regular syntax
	  case Lam(name, ty, t) => Lam(name, ty, shift(t, d, c+1))
      case App(t1, t2) =>  App(shift(t1, d, c), shift(t2, d, c))  
      
      //SAN: Added special syntax
      case Let(name, ty, t, b) => Let(name, ty,t, shift(b,d,c+1))
      case TArr(t1,t2) => TArr(shift(t1, d, c),shift(t2, d, c))
      case Pi(name,t1,t2) => Pi(name,t1,shift(t2, d, c+1))
      case Set => Set
      case Ann(t1,t2) => Ann(shift(t1, d, c),shift(t2, d, c))
      
	  //SAN: Bools
      case Bool => Bool
      case True => True 
      case False => False
      case IfThenElse(t1, t2, t3) => IfThenElse(shift(t1, d, c), shift(t2, d, c), shift(t3, d, c)) 

	  //SAN: Nats
	  case Nat => Nat
	  case Zero => Zero
      case Succ(t1) => Succ(shift(t1, d, c))
      case Pred(t1) => Pred(shift(t1, d, c))
      case IsZero(t1) => IsZero(shift(t1, d, c))
      case NatInd => NatInd
      
      //SAN: Unit
      case TUnit => TUnit
      case Unit => Unit
      
      //SAN: Sigma types
      case Sigma(name,t1,t2) => Sigma(name,shift(t1,d,c), shift(t2,d,c))
      case Pair(t1,t2) => Pair(shift(t1, d, c),shift(t2, d, c))
      case First(t1) => First(shift(t1, d, c))
      case Second(t1) => Second(shift(t1, d, c))
      
	  case _      => t
	}

	//SAN TODO: add other cases (*incomplete*)
	//	we could skip the terms that don't have anything to subst.
	def subst(t:Term, v:Int, s:Term) : Term = t match {
	  case Var(i) => if (i==v) s else Var(i)
	  
	   //SAN: Regular syntax
	  case Lam(name, ty, t1) => Lam(name, ty, subst(t1, v+1, shift(s,1,0)))
      case App(t1, t2) =>  App(subst(t1, v, s), subst(t2, v, s))  
      
      //SAN: Added special syntax
      case Let(name, t1, t2, t3) => Let(name, subst(t1, v, s),subst(t2, v, s),
    		  							subst(t3,v+1,shift(s,1,0)))
      case TArr(t1,t2) => TArr(subst(t1, v, s),subst(t2, v, s))
      case Pi(name,t1,t2) => Pi(name,subst(t1, v, s),subst(t2, v+1, shift(s,1,0)))
      case Set => Set
      case Ann(t1,t2) => Ann(subst(t1, v, s),subst(t2, v, s))
      
	  //SAN: Bools
      case Bool => Bool
      case True => True 
      case False => False
      case IfThenElse(t1, t2, t3) => IfThenElse(subst(t1, v, s), subst(t2, v, s), subst(t3, v, s)) 

	  //SAN: Nats
	  case Nat => Nat
	  case Zero => Zero
      case Succ(t1) => Succ(subst(t1, v, s))
      case Pred(t1) => Pred(subst(t1, v, s))
      case IsZero(t1) => IsZero(subst(t1, v, s))
      case NatInd => NatInd
      
      //SAN: Unit
      case TUnit => TUnit
      case Unit => Unit
      
      //SAN: Sigma types
      case Sigma(name,t1,t2) => Sigma(name,subst(t1,v,s), subst(t2,v,s))
      case Pair(t1,t2) => Pair(subst(t1, v, s),subst(t2, v, s))
      case First(t1) => First(subst(t1, v, s))
      case Second(t1) => Second(subst(t1, v, s))
      
	  case _      => t
	}
	
    def termSubstTop(s:Term, t:Term): Term = { // see Pierce p 385
      shift(subst(t,0,shift(s,1, 0)),-1,0)
    }

    /**
     * Sven's Additional Notes (SAN):
     * 
     * I think that here we should add that terms are also evaluated during typechecking.
     *  Typechecker requires support for "evaluation under assumptions", i.e., it must evaluate 'inside' or 'under' abstractions
     *  We are free to experiment with different evaluation strategies( call-by-value, by-name-, by-need...)
     */
    
    //TODO: add other cases
	def eval1[R](t:Term): Option[Term] = {
	  //SAN: I added the nosuchelementexception try/catch
	  try{
	  t match {
		  case App(Lam(_,a,t),s) => Some(termSubstTop(s,t))	//E-AppAbs
		  
				  //SAN Basic E-rules
		  case Lam(x,t1,t2) if eval1(t2) != None => Some(Lam(x,t1,eval(t2))) //E-Abs1
		  case Lam(x,t1,t2) if eval1(t1.get) != None 
		  				=> Some(Lam(x,eval1(t1.get),t2)) //E-Abs2
		  case Pi(v, t1, t2) if eval1(t2) != None => Some(Pi(v,t1,eval(t2))) //E-Pi1
		  case Pi(v, t1, t2) if eval1(t1) != None => Some(Pi(v,eval(t1),t2)) //E-Pi2
		  case App(t1,t2) if eval1(t2) != None => Some(App(t1,eval(t2))) //E-App1
		  case App(t1,t2) if eval1(t1) != None => Some(App(eval(t1),t2)) //E-Abs2
		 
		  		  //SAN  Bools
		  case IfThenElse(True,t2,t3) => Some(t2) //E-IfTrue
		  case IfThenElse(False,t2,t3) => Some(t3)	//E-IfFalse
		  case IfThenElse(t1,t2,t3) if eval1(t1) != None 
		  			=> Some(IfThenElse(eval1(t1).get,t2,t3))//E-If1
		  case IfThenElse(t1,t2,t3) if eval1(t2) != None 
		  			=> Some(IfThenElse(t1,eval1(t2).get,t3))//TODO E-If2
		  case IfThenElse(t1,t2,t3) if eval1(t3) != None 
		  			=> Some(IfThenElse(t1,t2,eval1(t3).get))//TODO E-If3
		  
		  		//SAN Nats
		  case Succ(t) if eval(t) != None => Some(Succ(eval1(t).get)) // E-succ
		  case Pred(Zero) => Some(Zero) //E-PredZero
		  case Pred(Succ(t)) => Some(t)	//E-PredSucc
		  case Pred(t) if eval(t) != None => Some(Pred(eval1(t).get))// E-Pred
		  case IsZero(Zero) => Some(True)	//E-IsZeroZero
		  case IsZero(Succ(t)) => Some(False)	// E-IsZeroSucc
		  case IsZero(t) if eval(t) != None => Some(IsZero(eval1(t).get))// E-IsZero
		  
		  		//SAN Sigma types
		  case First(Pair(s,t)) => Some(s)	//E-Fst
		  case Second(Pair(s,t)) => Some(t)	//E-Snd
		  
		  		//SAN Let
		  case  Let(x,t1,t2,t3) => Some(termSubstTop(t2,t3))	//E-Let
		  
		  		//SAN NatInd TODO
		  
		  		//SAN todo subst

		  case _ => None
	  }
	  } catch{
	    case e : NoSuchElementException => None
	  }
	}
	
    def eval(t:Term): Term = { // evaluation until weak head normal form
      eval1(t) match {
        case Some(t1) => eval(t1)
        case None     => t
      }
    }
    
    /**
     * Sven's Additional Notes (SAN):
     *
     * All terms in a DTLC normalize. 
     */
    //TODO: implement full beta reduction
    def normalize(t:Term): Term = t 
}