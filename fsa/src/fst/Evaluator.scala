package fst

import Syntax._

class Evaluator {
  
	//TODO: add other cases
	def shift(t:Term, d:Int, c:Int): Term = t match {
	  case Var(i) => if (i<c) Var(i) else Var(i+d)
	  case _      => t
	}

	//TODO: add other cases
	def subst(t:Term, v:Int, s:Term) : Term = t match {
	  case Var(i) => if (i==v) s else Var(i)
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
	  t match {
		  case App(Lam(_,a,t),s) => Some(termSubstTop(s,t))
		  case _ => None
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