package fst

import Syntax._
import java.util.NoSuchElementException

/**
 * @author Sven Akkermans and Toon Nolten
 */
class Evaluator {
	
	//	we could skip the terms that don't have anything to shift, for clarity we don't.
	def shift(t:Term, d:Int, c:Int): Term = t match {

	  case Var(i) => if (i<c) Var(i) else Var(i+d)
	  
	  case Lam(name, ty, t) => Lam(name, ty, shift(t, d, c+1))
      case App(t1, t2) =>  App(shift(t1, d, c), shift(t2, d, c))  
      
      case Let(name, ty, t, b) => Let(name, ty,t, shift(b,d,c+1))
      case TArr(t1,t2) => TArr(shift(t1, d, c),shift(t2, d, c))
      case Pi(name,t1,t2) => Pi(name,shift(t1, d, c),shift(t2, d, c+1))
      case Set => Set
      case Ann(t1,t2) => Ann(shift(t1, d, c),shift(t2, d, c))
      
	  //Bools
      case Bool => Bool
      case True => True 
      case False => False
      case IfThenElse(t1, t2, t3) => IfThenElse(shift(t1, d, c), shift(t2, d, c), shift(t3, d, c)) 

	  //Nats
	  case Nat => Nat
	  case Zero => Zero
      case Succ(t1) => Succ(shift(t1, d, c))
      case Pred(t1) => Pred(shift(t1, d, c))
      case IsZero(t1) => IsZero(shift(t1, d, c))
      case NatInd => NatInd
      
      //Unit
      case TUnit => TUnit
      case Unit => Unit
      
      //Sigma types
      case Sigma(name,t1,t2) => Sigma(name,shift(t1,d,c), shift(t2,d,c+1))
      case Pair(t1,t2) => Pair(shift(t1, d, c),shift(t2, d, c))
      case First(t1) => First(shift(t1, d, c))
      case Second(t1) => Second(shift(t1, d, c))
      
	  case _      => t
	}

	//	we could skip the terms that don't have anything to subst, for clarity we don't.
	def subst(t:Term, v:Int, s:Term) : Term = t match {
	  case Var(i) => if (i==v) s else Var(i)
	  
	  case Lam(name, None, t1) => Lam(name, None, subst(t1, v+1, shift(s,1,0)))
	  case Lam(name, Some(ty), t1) => Lam(name, Some(subst(ty,v,s)), subst(t1, v+1, shift(s,1,0)))
      case App(t1, t2) =>  App(subst(t1, v, s), subst(t2, v, s))  
      
      case Let(name, t1, t2, t3) => Let(name, subst(t1, v, s),subst(t2, v, s),
    		  							subst(t3,v+1,shift(s,1,0)))
      case TArr(t1,t2) => TArr(subst(t1, v, s),subst(t2, v, s))
      case Pi(name,t1,t2) => Pi(name,subst(t1, v, s),subst(t2, v+1, shift(s,1,0)))
      case Set => Set
      case Ann(t1,t2) => Ann(subst(t1, v, s),subst(t2, v, s))
      
	  //Bools
      case Bool => Bool
      case True => True 
      case False => False
      case IfThenElse(t1, t2, t3) => IfThenElse(subst(t1, v, s), subst(t2, v, s), subst(t3, v, s)) 

	  //Nats
	  case Nat => Nat
	  case Zero => Zero
      case Succ(t1) => Succ(subst(t1, v, s))
      case Pred(t1) => Pred(subst(t1, v, s))
      case IsZero(t1) => IsZero(subst(t1, v, s))
      case NatInd => NatInd
      
      //Unit
      case TUnit => TUnit
      case Unit => Unit
      
      //Sigma types
      case Sigma(name,t1,t2) => Sigma(name,subst(t1,v,s), subst(t2,v+1,shift(s,1,0)))
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
    
	def eval1[R](t:Term): Option[Term] = {
	  try{
	  t match {
		  //NatInd
		  case App(App(App(App(NatInd,p),base),step),Zero) => Some(eval(base)) // E-natIndZero
		  case App(App(App(App(NatInd,p),base),step),Succ(n)) 			// E-natIndNotZero
		  	=> Some(App(eval(App(step, n)), eval(App(App(App(App(NatInd,p),base),step),n))))
		  case App(App(App(App(NatInd,p),base),step),n) if eval1(n) != None			// congruence
		  	=> Some(App(App(App(App(NatInd,p),base),step),eval(n)))
		  	
		  //BoolElim
		  case App(App(App(App(BoolElim,p),ptrue),pfalse),True) => Some(ptrue) //E-BoolElimTrue
		  case App(App(App(App(BoolElim,p),ptrue),pfalse),False) => Some(pfalse) //E-BoolElimFalse
		  case App(App(App(App(BoolElim,p),ptrue),pfalse),b) if eval1(b) != None => Some(App(App(App(App(BoolElim,p),ptrue),pfalse),eval(b))) //E-BoolElim

		  //Identity
		  case App(App(App(App(App(App(Subst,a),x),y),p),App(App(Refl,b),z)),px) if a == b => Some(px)

		  case App(Lam(n,a,t),s) => Some(termSubstTop(s,t))	//E-AppAbs
		  
		  //Basic E-rules
		  case Lam(x,t1,t2) if eval1(t2) != None => Some(Lam(x,t1,eval(t2))) //E-Abs1
		  case Lam(x,t1,t2) if eval1(t1.get) != None 
		  				=> Some(Lam(x,eval1(t1.get),t2)) //E-Abs2
		  case Pi(v, t1, t2) if eval1(t2) != None => Some(Pi(v,t1,eval(t2))) //E-Pi1
		  case Pi(v, t1, t2) if eval1(t1) != None => Some(Pi(v,eval(t1),t2)) //E-Pi2
		  case App(t1,t2) if eval1(t2) != None => Some(App(t1,eval(t2))) //E-App1
		  case App(t1,t2) if eval1(t1) != None => Some(App(eval(t1),t2)) //E-App2
		 
		  //Bools
		  case IfThenElse(True,t2,t3) => Some(t2) //E-IfTrue
		  case IfThenElse(False,t2,t3) => Some(t3)	//E-IfFalse
		  case IfThenElse(t1,t2,t3) if eval1(t1) != None 
		  			=> Some(IfThenElse(eval1(t1).get,t2,t3))//E-If1
		  case IfThenElse(t1,t2,t3) if eval1(t2) != None 
		  			=> Some(IfThenElse(t1,eval1(t2).get,t3))// E-If2
		  case IfThenElse(t1,t2,t3) if eval1(t3) != None 
		  			=> Some(IfThenElse(t1,t2,eval1(t3).get))// E-If3
		  
		  //Nats
		  case Succ(t) if eval1(t) != None => Some(Succ(eval(t))) // E-succ
		  case Pred(Zero) => Some(Zero) //E-PredZero
		  case Pred(Succ(t)) => Some(t)	//E-PredSucc
		  case Pred(t) if eval1(t) != None => Some(Pred(eval(t)))// E-Pred
		  case IsZero(Zero) => Some(True)	//E-IsZeroZero
		  case IsZero(Succ(t)) => Some(False)	// E-IsZeroSucc
		  case IsZero(t) if eval1(t) != None => Some(IsZero(eval(t)))// E-IsZero
		  
		  //Sigma types
		  case Sigma(name, s, t) if eval1(s) != None => Some(Sigma(name, eval(s), t))
		  case Sigma(name, s, t) if eval1(t) != None => Some(Sigma(name, s, eval(t)))
		  /*case Ann(Pair(s, t), Sigma(name, s_ty, t_ty)) if eval1(s_ty) != None => Some(Ann(Pair(s,t), Sigma(name, eval(s_ty), t_ty)))
  		  case Ann(Pair(s, t), Sigma(name, s_ty, t_ty)) => Some(Ann(Pair(s,t), Pair(s_ty, termSubstTop(s, t_ty))))
  		  case Ann(Pair(s, t), Pair(s_ty, t_ty)) if eval1(t_ty) != None => Some(Ann(Pair(s, t), Pair(s_ty, eval(t_ty))))*/
		  case Pair(s, t) if eval1(s) != None => Some(Pair(eval(s), t))
		  case Pair(s, t) if eval1(t) != None => Some(Pair(s, eval(t)))
		  case First(Pair(s,t)) => Some(s)	//E-Fst
		  case Second(Pair(s,t)) => Some(t)	//E-Snd
		  case First(p) if eval1(p) != None => Some(First(eval(p)))
		  case Second(p) if eval1(p) != None => Some(Second(eval(p)))

		  
		  // Let
		  case  Let(x,t1,t2,t3) => Some(termSubstTop(t2,t3))	//E-Let
		  
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
    
    // Since we do call-by-value, normalize doesn't have a real purpose and we haven't expanded upon it further. 
    def normalize(t:Term): Term = {
      t match {
        case App( Lam(name, ty, t1), t2) => subst(t2, 1, t1) //Beta-AppAbs
        case _ => t
      }
     
    }
}