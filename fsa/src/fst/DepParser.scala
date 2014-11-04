package fst

import scala.util.parsing.combinator.syntactical.StdTokenParsers
import scala.util.parsing.combinator.lexical.StdLexical

/**
 * A generic parser for dependently typed languages.
 * 
 * The syntax may look similar to normal lambda calc syntaxes, but
 * it is technically so different that it's easier to separate them.
 * 
 * To use this, define a subclass of Calculus[Term,Term,Unit] (this
 * means a calculus where there is no distinction between terms and
 * types and without constraints) and implement the required
 * constructs. Then you can call parseTerm below to parse strings to
 * terms.   
 * 
 * Based on previous code by Dominique Devriese and Adriaan Moors.
 * 
 * @author Jesper Cockx.
 */
class DepParser[Term](calc : Calculus[Term,Term,Unit]) extends StdTokenParsers {
	type Tokens = StdLexical
	val lexical = new StdLexical

	case class UnknownIdentifierException(s: String) extends Exception {
	  override def toString = "Unknown identifier: '" + s + "'";
	}
	def ctxindex(ls:List[String],s:String) : Int = {
	  val i = ls.indexOf(s);
	  if(i == -1) throw new UnknownIdentifierException(s);
	  else i;
	}
	
	type Context = List[String];
	
	lexical.delimiters ++= List("(", ")", ":", ".", "\\",",","->","[","]","!", ":=", "=", ";")
	lexical.reserved ++=List("true","false","if","then","else","succ","pred","iszero","Bool","Nat","All","let","fix","ref","unit","Unit","Ref","in","natInd","Ref","raise","try","with", "class", "instance", "where","Eq","eq","Set","I","refl","subst","Bot","boolElim","trustMe","Sigma","fst","snd")

    // TERMS							 	
	def term(ctx:Context): Parser[Term] = 
	    ("(" ~> ident <~ ":") ~ (term(ctx) <~ ")" <~ "->") >> { case v~ty1 => term(v::ctx) ^^ (ty2 => calc.mkPi(v,ty1,ty2))} |
		("Sigma" ~> "[" ~> ident <~ ":") ~ (term(ctx) <~ "]") >> { case v~ty1 => term(v::ctx) ^^ (ty2 => calc.mkSigma(v,ty1,ty2))} |
		("\\" ~> ident <~ ":") ~ (term(ctx) <~ ".") >> { case v~ty => term(v::ctx) ^^ (t => calc.mkAbs(v,Some(ty),t)) } | 	    // \x:T. term, binds (x,T) in the context
		("\\" ~> ident <~ ".") >> { v => term(v::ctx) ^^ (t => calc.mkAbs(v,None,t)) } | 
		("let" ~> ident <~ ":") ~ (term(ctx) <~ "=") ~ (term(ctx) <~ "in") >> { case v~ty~vi => term(v::ctx) ^^ (t => calc.mkLet(v,ty,vi,t)) } |	// let x: T = y in term, binds (x,T) in the context of term	
		    app(ctx) ~ opt("->" ~> term(ctx)) ^^ { case t ~ None => t
											       case t1 ~ Some(t2) => calc.mkTArr(t1,t2)
											     }
	
    def app(ctx:Context): Parser[Term] = 																			 	// t1 t2 t3 ... , left associative application
		baseterm(ctx)~rep(baseterm(ctx)) ^^ { case t ~ Nil => t
    								   		  case t ~ l => (t/:l)( (x,y) => calc.mkApp(x,y))
										     }

	def baseterm(ctx:Context) = numericLit ^^ (s => calc.mkNatLit(s.toInt)) |
								"I" ^^ (_ => calc.mkI) |
								"refl" ^^ (_ => calc.mkRefl) |
								"subst" ^^ (_ => calc.mkSubst) |
								"true" ^^ (_ => calc.mkTrue) |
								"eq" ^^ (_ => calc.mkEq) |
								"unit" ^^ (_ => calc.mkUnit) |
								"false" ^^ (_ => calc.mkFalse) |
								"if" ~> term(ctx) ~ "then" ~ term(ctx) ~ "else" ~ term(ctx) ^^ { case t1~"then"~t2~"else"~t3 => calc.mkIfThenElse(t1,t2,t3) } |
								"succ" ~> term(ctx) ^^ (t => calc.mkSucc(t)) |
								"fix" ~> term(ctx) ^^ (t => calc.mkFix(t)) |
								"pred" ~> term(ctx) ^^ (t => calc.mkPred(t)) |
								"iszero" ~> term(ctx) ^^ (t => calc.mkIsZero(t)) |
								"natInd" ^^ { _ => calc.mkNatInd} |
								("(" ~> term(ctx) <~ ",") ~ term(ctx) <~ ")" ^^ { case t1~t2 => calc.mkPair(t1,t2) } |
								"fst" ~> term(ctx) ^^ (t => calc.mkFirst(t)) |
								"snd" ~> term(ctx) ^^ (t => calc.mkSecond(t)) |
								"Unit" ^^ (_ => calc.mkTUnit) |
								"Bool" ^^ (_ => calc.mkBool) |
								"Nat"  ^^ (_ => calc.mkNat) |
								"Set" ^^ (_ => calc.mkSet) |
								"Bot" ^^ (_ => calc.mkTBot) |
								"boolElim" ^^ (_ => calc.mkBoolElim) |
								"trustMe" ^^ (_ => calc.mkTrustMe(None)) |
								ident ^^ (s=> { calc.mkVar(ctxindex(ctx,s)) }) |
								("(" ~> term(ctx) <~ ":") ~ (term(ctx) <~ ")") ^^ { case t~ty => calc.mkAnnot(ty,t) } |
								"("~>term(ctx)<~")" 
	
	case class IncompleteParseException(parsedTerm:Term) extends Exception;
	case class FailedParseException(failure:ParseResult[Term]) extends Exception;

	def parseTerm(s : String) : Term = {
	  term(Nil)(new lexical.Scanner(s)) match {
                  case Success(r,next) if (next.atEnd) => r;
                  case Success(r,next) => 
                    throw new IncompleteParseException(r);
                  case failure => throw new FailedParseException(failure);
         }
	}
}
