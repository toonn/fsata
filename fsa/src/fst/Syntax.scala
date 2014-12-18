package fst

import scala.xml.PrettyPrinter
/**
 * @author Sven Akkermans and Toon Nolten
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
  
	sealed abstract class Term {
	  def atomic : Boolean = true
	  def prettyPrint(): String = prettyPrint(List())
	  def prettyPrint(names: Names): String
	  def prettyPrintP(names: Names): String = if (atomic) prettyPrint(names) else "(" + prettyPrint(names) + ")"
	}
	
	// Basic language
	case class Var(i : Int) extends Term { 
	  override def prettyPrint(names: Names) = names(i)
	}
	
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
	
	case object Set extends Term {
	  override def prettyPrint(names: Names) = "Set"
	}
	
	// Practical matters
	case class Ann(a : Term, t : Term) extends Term { 
	  override def atomic = false
	  override def prettyPrint(names: Names) = "(" + t.prettyPrint(names) + " : " + a.prettyPrint(names) + ")"
	}
	
	case object notImplemented extends Term {
	  override def prettyPrint(names: Names) = "notImplemented"
	}
	
	case object Nat extends Term {
	  override def prettyPrint(names: Names) = "Nat"
	}
	case object Zero extends Term {
	  override def prettyPrint(names: Names) = "0"
	}
	case class Succ(e: Term) extends Term {
	  override def atomic = false
	  override def prettyPrint(names: Names) = 
		  "succ " + e.prettyPrint(names)  
	}
	case class Pred(e: Term) extends Term {
	  override def atomic = false
	  override def prettyPrint(names: Names) = 
		  "pred " + e.prettyPrint(names)  
	}
	case class IsZero(e: Term) extends Term {
	  override def atomic = false
	  override def prettyPrint(names: Names) = 
		  "isZero " + e.prettyPrint(names)  
	}
	case object NatInd extends Term {
	  override def atomic = false
	  override def prettyPrint(names: Names) = 
		"natInd"
	}
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
	  override def atomic = false
	  override def prettyPrint(names: Names) = 
		  "if " + c.prettyPrint(names) + " then " + e1.prettyPrint(names) + " else " + e2.prettyPrint(names)				  
	}
	case class Sigma(v: String, a: Term, b: Term) extends Term {
	  override def atomic = false
	  override def prettyPrint(names: Names) = 
		  "Sigma[ " + v + " : " + a.prettyPrint(names) + " ] " + b.prettyPrint(names)				  
	}
	case class Pair(s: Term, t: Term) extends Term {
	  override def atomic = false
	  override def prettyPrint(names: Names) = 
		  "(" + s.prettyPrint(names) + "," + t.prettyPrint(names) + ")"			  
	}
	case class First(t: Term) extends Term {
	  override def atomic = false
	  override def prettyPrint(names: Names) = "fst " + t.prettyPrint(names)  
	}
	case class Second(t: Term) extends Term {
	  override def atomic = false
	  override def prettyPrint(names: Names) = "snd " + t.prettyPrint(names)
	}
	case object TUnit extends Term {
	  override def prettyPrint(names: Names) = "Unit"
	}
	case object Unit extends Term {
	  override def prettyPrint(names: Names) = "unit"
	}
	case class Let(v: String, ty: Term, vi: Term, t: Term) extends Term{
	  override def atomic = false
	  override def prettyPrint(names: Names) = 
		  "let" + v + " : " + ty.prettyPrint(names) + " = " + 
				  vi.prettyPrint(names) + " in " + t.prettyPrint(names)
	}
	case class TArr(t1: Term, t2: Term) extends Term{
	  override def atomic = false
	  override def prettyPrint(names: Names) = 
		  "(" + t1.prettyPrint(names) + " -> " + t2.prettyPrint(names) + " )"
	}
	case object I extends Term {
	  override def prettyPrint(names: Names) = "I"
	}
	case object Refl extends Term {
	  override def prettyPrint(names: Names) = "refl"
	}
	case object Subst extends Term {
	  override def prettyPrint(names: Names) = "subst"
	}
	case object BoolElim extends Term {
	  override def prettyPrint(names: Names) = "boolElim"
	}
}