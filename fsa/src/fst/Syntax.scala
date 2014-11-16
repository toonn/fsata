package fst

import scala.xml.PrettyPrinter
/**
 * 
 * @author Akkermans Sven and Nolten Toon
 */
object Syntax {

    type Names = List[String]
    
    type Context = List[(String,Term)]
	
	def toNames(ctx: Context): Names = ctx.map(x => x._1)
		
	def lookupName(d: Int,ctx: Context): String = {
	  ctx(d)._1
	}
	
	def uniqueName(name: String, names: Names): String = {
	  if (names.contains(name)) {
	    uniqueName(name, 1, names)
	  } else {
	    name
	  }
	}
	
	def uniqueName(name: String, i: Int, names: Names): String = {
	  if(names.contains(name+i)) {
	    uniqueName(name,i+1,names)
	  } else {
	    name + i
	  }
	}
  
	/**
	 * Sven's Additional Notes (SAN):	 
	 * 
	 *  No distinguishment brtween types and terms
	 *  Types are a subset of terms.
	 */	
	sealed abstract class Term {
	  def atomic : Boolean = true
	  def prettyPrint(): String = prettyPrint(List())
	  def prettyPrint(names: Names): String
	  def prettyPrintP(names: Names): String = if (atomic) prettyPrint(names) else "(" + prettyPrint(names) + ")"
	}
	
	/**
	 * Sven's Additional Notes (SAN):
	 * 
	 * This section corresponds to Basic Syntax from assignment.
	 */
	// Basic language
	case class Var(i : Int) extends Term { 
	  override def prettyPrint(names: Names) = names(i)
	}
	
	//SAN: Abstraction: \ x : a . t
	//		'name' is the Symbol (variable), t is the body (term)
	//		'a' is the type of the variable bound and can be omitted
	//				similar as unannotated lambdas: \ x . t
	case class Lam(name : String, a : Option[Term], t : Term) extends Term { 
	  override def atomic = false
	  override def prettyPrint(names: Names) = {
	    val name1 = uniqueName(name,names)
	    a match {
	    	case Some(a1) => "\\" + name1 + ":"+ a1.prettyPrint(names) +". " + t.prettyPrint(name1::names) 
	    	case None     => "\\" + name1 + ". " + t.prettyPrint(name1::names) 
	    }
	  }
	}
	case class App(f : Term, t : Term) extends Term { 
	  override def atomic = false
	  override def prettyPrint(names: Names) = f match {
	    case App(g,s) => f.prettyPrint(names) + " " + t.prettyPrintP(names)
	    case _        => f.prettyPrintP(names) + " " + t.prettyPrintP(names)
	  }
	}
	
	// SAN: New wrt STLC 'dependent function types'
	case class Pi(name: String, a : Term, b : Term) extends Term {
	  override def atomic = false
	  override def prettyPrint(names: Names) = {
	    
	    if (name == "_") {
	      a.prettyPrint(names) + " -> " + b.prettyPrint(name::names)
	    } else {
	      val name1 = uniqueName(name,names)
	      "(" + name1 + " : " + a.prettyPrint(names) + ") -> " + b.prettyPrint(name1::names)
	    }
	  }
	}
	
	// SAN: New wrt STLC 'type of types'
	case object Set extends Term {
	  override def prettyPrint(names: Names) = "Set"
	}
	
	// Practical matters
	case class Ann(a : Term, t : Term) extends Term { 
	  override def prettyPrint(names: Names) = "(" + t.prettyPrint(names) + " : " + a.prettyPrint(names) + ")"
	}
	
	case object notImplemented extends Term {
	  override def prettyPrint(names: Names) = "notImplemented"
	}
	
    ////////////////////////////////////////
    //SAN  Additions: underneath this line//
    ////////////////////////////////////////		
		//SAN: the nats
	case object Nat extends Term {
	  override def prettyPrint(names: Names) = "Nat"
	}
	case object Zero extends Term {
	  override def prettyPrint(names: Names) = "0"
	}
	case class Succ(e: Term) extends Term {
		override def prettyPrint(names: Names) = 
		  "succ " + e.prettyPrint(names)  
	}
	case class Pred(e: Term) extends Term {
		override def prettyPrint(names: Names) = 
		  "pred " + e.prettyPrint(names)  
	}
	case class IsZero(e: Term) extends Term {
		override def prettyPrint(names: Names) = 
		  "isZero " + e.prettyPrint(names)  
	}
		//SAN: the bools
	case object Bool extends Term {
	  override def prettyPrint(names: Names) = "Bool"
	}
	case object True extends Term {
	  override def prettyPrint(names: Names) = "true"
	}
	case object False extends Term {
	  override def prettyPrint(names: Names) = "false"
	}
	case class IfThenElse(c: Term, e1: Term, e2: Term) extends Term {
		override def prettyPrint(names: Names) = 
		  "if " + c.prettyPrint(names) + " then " + e1.prettyPrint(names) + " else " + e2.prettyPrint(names)				  
	}	

	
	//SAN: Todo implement
	case object Let extends Term{
	  	  override def prettyPrint(names: Names) = "notImplemented"
	}

		
}