package fst

import fst.Syntax._
import org.scalatest.junit.JUnitRunner
import org.junit.runner.RunWith
import org.scalatest.matchers.ShouldMatchers
import org.scalatest.FunSuite

@RunWith(classOf[JUnitRunner])
class DepTest extends FunSuite with ShouldMatchers {
	val calc = new DepCalculus();
	val parser = new DepParser(calc);
	val eval = new Evaluator;
	val typer = new Typer(eval);

	type Term = calc.Term
	
	var i = 1;

	def evaluateAndTypeTest(in:String, ty: Term, out: Term) = {
        test("type and evaluate expression " + i) {
            System.out.print("Parsing expression: " + in)
            val e : Term = parser.parseTerm(in);
            println(" ### " + e)
            System.out.println(" (OK)")
            if(ty != null) {
                System.out.print("Checking that " + e + " has type " + ty)
                val (t1, ty1) = typer.tcTerm(e,Some(ty),Nil)
                System.out.println(" (OK)")
                if(out != null) { 
                  System.out.print("Checking if " + eval.eval(t1).prettyPrint() + " is equal to " + out.prettyPrint())
                  typer.equalTerms(t1,out,Nil) should be ===true 
                  System.out.println(" (OK)")
                }
            } else { 
                evaluating {typer.typeOf(e,Nil)} should produce [TypeException];
            }
        }
        i = i + 1
    }
		
	// basic calculus
		//test 1
	evaluateAndTypeTest("Set", calc.mkSet, calc.mkSet)
	evaluateAndTypeTest("""(\A : Set. Set) Set""", calc.mkSet, calc.mkSet)
	
	// general lambda calculus stuff...
	evaluateAndTypeTest("Nat", calc.mkSet, calc.mkNat);	
		//test 3
	evaluateAndTypeTest("Bool", calc.mkSet, calc.mkBool);	
	evaluateAndTypeTest("true", calc.mkBool, calc.mkTrue);	
	evaluateAndTypeTest("false", calc.mkBool, calc.mkFalse);	
	evaluateAndTypeTest("0", calc.mkNat, calc.mkZero);	
	evaluateAndTypeTest("succ 0", calc.mkNat, calc.mkSucc(calc.mkZero));
		//test 9
	evaluateAndTypeTest("Set", calc.mkSet, calc.mkSet);	
	
	// t_1 -> t_2 === (_ : t_1) -> t_2
	evaluateAndTypeTest("""Bool -> Bool""", calc.mkSet, calc.mkPi("_",calc.mkBool, calc.mkBool));
	// shift properly during the translation
	evaluateAndTypeTest("""Bool -> (A : Set) -> A""", calc.mkSet, calc.mkPi("_",calc.mkBool, calc.mkPi("A", calc.mkSet, calc.mkVar(0))));
	evaluateAndTypeTest("""(A : Set) -> Bool -> A""", calc.mkSet, calc.mkPi("A", calc.mkSet, calc.mkPi("_",calc.mkBool, calc.mkVar(1))));
	
	// alpha-equivalence
		//test 13
    evaluateAndTypeTest("""(x:Nat) -> Nat""", calc.mkSet, calc.mkPi("y",calc.mkNat,calc.mkNat)); 
		//test 14
    evaluateAndTypeTest("""\A:Set.A""",calc.mkPi("B",calc.mkSet,calc.mkSet), calc.mkAbs("B",Some(calc.mkSet),calc.mkVar(0)));
	
	evaluateAndTypeTest("""\x:Nat.0""", calc.mkTArr(calc.mkNat,calc.mkNat), calc.mkAbs("x",Some(calc.mkNat),calc.mkZero));	
	evaluateAndTypeTest("""\x:Nat.succ x""", calc.mkTArr(calc.mkNat,calc.mkNat), calc.mkAbs("x",Some(calc.mkNat),calc.mkSucc(calc.mkVar(0))));
	evaluateAndTypeTest("""Nat -> Nat""", calc.mkSet, calc.mkTArr(calc.mkNat,calc.mkNat));	
	evaluateAndTypeTest("""(\x:Nat.0) 0""", calc.mkNat, calc.mkZero);	
		//test 19
	evaluateAndTypeTest("let x : Bool = true in x", calc.mkBool, calc.mkTrue);
	evaluateAndTypeTest("let x : Bool = true in (if x then 3 else 2)", calc.mkNat, calc.mkNatLit(3));
	evaluateAndTypeTest("succ 0 ", calc.mkNat, calc.mkNatLit(1));
	evaluateAndTypeTest("succ (pred 0)", calc.mkNat, calc.mkNatLit(1));
	evaluateAndTypeTest("if true then false else true", calc.mkBool,calc.mkFalse);
		//test 24
	evaluateAndTypeTest("iszero pred 0", calc.mkBool, calc.mkTrue);
	evaluateAndTypeTest("if iszero pred 0 then succ 0 else pred succ 0", calc.mkNat, calc.mkNatLit(1));
	evaluateAndTypeTest("if iszero 0 then succ 0 else 0", calc.mkNat, calc.mkNatLit(1));
	evaluateAndTypeTest("if iszero succ 0 then true else false",calc.mkBool,calc.mkFalse);
		//test 28
	evaluateAndTypeTest("0",calc.mkNat,calc.mkZero);
	evaluateAndTypeTest(""" \x:Bool. \y:Bool.x """, 
			calc.mkPi("_",calc.mkBool,calc.mkPi("_",calc.mkBool,calc.mkBool)),calc.mkAbs("x",Some(calc.mkBool),calc.mkAbs("y",Some(calc.mkBool),calc.mkVar(1)))); // the encoded boolean true over the Bool type
	evaluateAndTypeTest(""" \x:Bool. \y:Bool.y """, 
			calc.mkPi("_",calc.mkBool,calc.mkPi("_",calc.mkBool,calc.mkBool)),calc.mkAbs("x",Some(calc.mkBool),calc.mkAbs("y",Some(calc.mkBool),calc.mkVar(0)))); // the encoded boolean false over the Bool type
	evaluateAndTypeTest(""" \b:Bool->Bool->Bool. \t:Bool. \f:Bool. b t f """, 
			calc.mkPi("_",calc.mkPi("_",calc.mkBool,calc.mkPi("_",calc.mkBool,calc.mkBool)),calc.mkPi("_",calc.mkBool,calc.mkPi("_",calc.mkBool,calc.mkBool))), 
			calc.mkAbs("b",Some(calc.mkPi("_",calc.mkBool,calc.mkPi("_",calc.mkBool,calc.mkBool))),calc.mkAbs("t",Some(calc.mkBool),calc.mkAbs("f",Some(calc.mkBool),calc.mkApp(calc.mkApp(calc.mkVar(2),calc.mkVar(1)),calc.mkVar(0))))));  // the conditional test
		//test 32
	evaluateAndTypeTest(""" (\b:Bool->Bool->Bool. \t:Bool. \f:Bool. b t f) (\x:Bool. \y:Bool.y) true false """, calc.mkBool, calc.mkFalse); // conditional applied to false
	evaluateAndTypeTest("""(\x:Bool. if x then 0 else 1) true""",calc.mkNat,calc.mkZero);
	evaluateAndTypeTest("""(\f:Nat->Nat. \n:Nat.f (f n)) (\n:Nat. succ n) 0""", calc.mkNat, calc.mkSucc(calc.mkSucc(calc.mkZero)));
	evaluateAndTypeTest("""(\f:Nat->Nat. \n:Nat.f (f n)) ((\f:Nat->Nat. \n:Nat.f (f n)) (\n:Nat. succ n)) 0""",
			calc.mkNat, calc.mkNatLit(4));

	// dependent types: basics
    	//test 36
	evaluateAndTypeTest("""(x:Nat) -> Nat""", calc.mkSet, calc.mkPi("x",calc.mkNat,calc.mkNat));	
	evaluateAndTypeTest("Set", calc.mkSet, calc.mkSet);
	
	// dependent types: polymorphism
		//test 38
	evaluateAndTypeTest("""(\A:Set.\x:A.x) Nat 0""",calc.mkNat,calc.mkZero);
	evaluateAndTypeTest("""(\A:Set.\x:A.x) Set Nat""",calc.mkSet,calc.mkNat);
	evaluateAndTypeTest("""(\P:Bool -> Set.\x:Bool.P x) (\x: Bool. if x then Nat else Bool) true""",calc.mkSet,calc.mkNat);
	evaluateAndTypeTest("""(\P:Bool -> Set.\x:P true.x) (\x: Bool. if x then Nat else Bool) 0""",calc.mkNat,calc.mkZero);
		//test 42
	evaluateAndTypeTest("""(\P:Bool -> Set.\x:P false.x) (\x: Bool. if x then Nat else Bool) false""",calc.mkBool,calc.mkFalse);	    
	evaluateAndTypeTest("""(\A:Set.\x:A.x) ((A : Set) -> A -> A) (\A:Set.\x:A.x) Nat 0""",calc.mkNat,calc.mkZero);
	
	//church encodings
		//test 43
	evaluateAndTypeTest("""let bool : Set = """ + calc.churchBoolDefinition + """ in
	                       let tru : bool = """ + calc.truDefinition + """ in
	                       let fls : bool = """ + calc.flsDefinition + """ in
	                       let not : bool -> bool = """ + calc.notDefinition + """ in
	                       let and : bool -> bool -> bool = """ + calc.andDefinition + """ in
	                       let or  : bool -> bool -> bool = """ + calc.orDefinition + """ in
	                       let bool_eq : bool -> bool -> bool = """ + calc.boolEqDefinition + """ in
	                       let toBool : bool -> Bool = \b. b Bool true false in
	                       toBool (and (or fls (not fls)) (bool_eq tru tru))
	                    """, calc.mkBool, calc.mkTrue) 
	                    
	evaluateAndTypeTest("""let nat : Set = """ + calc.churchNatDefinition + """ in
	                       let ze : nat = """ + calc.zeDefinition + """ in
	                       let su : nat -> nat = """ + calc.suDefinition + """ in
	                       let plus : nat -> nat -> nat = """ + calc.plusDefinition + """ in
	                       let toNat : nat -> Nat = \n. n Nat 0 (\x. succ x) in
	                       toNat (plus (su ze) (su ze))
	                    """, calc.mkNat, calc.mkNatLit(2))
	                    
	evaluateAndTypeTest("""let bool : Set = """ + calc.churchBoolDefinition + """ in
	                       let tru : bool = """ + calc.truDefinition + """ in
	                       let fls : bool = """ + calc.flsDefinition + """ in
	                       let nat : Set = """ + calc.churchNatDefinition + """ in
	                       let ze : nat = """ + calc.zeDefinition + """ in
	                       let su : nat -> nat = """ + calc.suDefinition + """ in
	                       let and : bool -> bool -> bool = """ + calc.andDefinition + """ in
	                       let isZero : nat -> bool = """ + calc.isZeroDefinition + """ in
	                       let toBool : bool -> Bool = \b. b Bool true false in
	                       toBool (and (isZero ze) (isZero (su ze)))
	                    """, calc.mkBool,calc.mkFalse)
	
	// natural induction...
	     //test 46
	evaluateAndTypeTest("""let plus : Nat -> Nat -> Nat = natInd (\n: Nat. Nat -> Nat) (\x : Nat. x) (\n:Nat.\h:Nat -> Nat.\v:Nat.succ (h v)) in
							plus 0 0""",calc.mkNat,calc.mkZero);
	evaluateAndTypeTest("""let plus : Nat -> Nat -> Nat = natInd (\n: Nat. Nat -> Nat) (\x : Nat. x) (\n:Nat.\h:Nat -> Nat.\v:Nat.succ (h v)) in
							plus 2 3""", calc.mkNat, calc.mkNatLit(5));
	evaluateAndTypeTest("""let plus : Nat -> Nat -> Nat = natInd (\n: Nat. Nat -> Nat) (\x : Nat. x) (\n:Nat.\h:Nat -> Nat.\v:Nat.succ (h v)) in
						   let times : Nat -> Nat -> Nat = """ + calc.timesDefinition + """ in
						   times 2 2""", calc.mkNat, calc.mkNatLit(4));
	evaluateAndTypeTest("""let pred2 : Nat -> Nat = """ + calc.pred2Definition + """ in
						   pred2 0""", calc.mkNat, calc.mkZero);
		//test 50
	evaluateAndTypeTest("""let pred2 : Nat -> Nat = """ + calc.pred2Definition + """ in
						   pred2 3""", calc.mkNat, calc.mkNatLit(2));
	evaluateAndTypeTest("""let pred2 : Nat -> Nat = """ + calc.pred2Definition + """ in
						   pred2 10""", calc.mkNat, calc.mkNatLit(9));
	evaluateAndTypeTest("""
	    let plus : Nat -> Nat -> Nat = natInd (\n: Nat. Nat -> Nat) (\x : Nat. x) (\n:Nat.\h:Nat -> Nat.\v:Nat.succ (h v)) in
		let oneton : Nat -> Nat = natInd (\n : Nat. Nat) 0 (\n : Nat. \s : Nat. plus n s) in
	    oneton 5
		""", calc.mkNat, calc.mkNatLit(10));

	// dependent if tests
		//test 53
	evaluateAndTypeTest("""let test : (x : Bool) -> if x then Nat else Bool = """ + calc.ifXThenNatElseBoolDefinition + """ in
	                       test false""", calc.mkBool, null);
	evaluateAndTypeTest("""let test : (x : Bool) -> if x then Nat else Bool = """ + calc.ifXThenNatElseBoolDefinition + """ in
	                       test true""", calc.mkNat, null);
	
	// sigma types
		//test 55
	evaluateAndTypeTest("""((1,1) : Sigma[ x : Nat ] Nat)""", calc.mkSigma("x", calc.mkNat, calc.mkNat), calc.mkPair(calc.mkNatLit(1),calc.mkNatLit(1)))
	evaluateAndTypeTest("""Sigma[ x : Nat ] Nat""", calc.mkSet, calc.mkSigma("x", calc.mkNat, calc.mkNat))
	evaluateAndTypeTest("""let plus : Nat -> Nat -> Nat = natInd (\n: Nat. Nat -> Nat) (\x : Nat. x) (\n:Nat.\h:Nat -> Nat.\v:Nat.succ (h v)) in
	                       let sum : (Sigma[ x : Nat ] Nat) -> Nat = \pair. plus (fst pair) (snd pair) in
	                       sum (2,3)""", calc.mkNat, calc.mkNatLit(5))
    evaluateAndTypeTest("""let plus : Nat -> Nat -> Nat = natInd (\n: Nat. Nat -> Nat) (\x : Nat. x) (\n:Nat.\h:Nat -> Nat.\v:Nat.succ (h v)) in 
                           let Vec : Set -> Nat -> Set = \A. natInd (\n. Set) Unit (\n. \H. Sigma[ _ : A ] H) in
                           let sum : (Sigma[ n : Nat ] Vec Nat n) -> Nat = \pair. natInd (\n. Vec Nat n -> Nat) (\_. 0) (\n. \h. \v. plus (fst v) (h (snd v))) (fst pair) (snd pair) in
                           sum  (3 , (1 , (2 , (3 , unit))))
                        """,calc.mkNat,calc.mkNatLit(6))
                        
    // identity types... 
         //test 59
	evaluateAndTypeTest("""let eqprf2 : I Nat 0 0 = refl Nat 0 in
			eqprf2""", calc.mkApp(calc.mkApp(calc.mkApp(calc.mkI,calc.mkNat),calc.mkZero),calc.mkZero),
			calc.mkApp(calc.mkApp(calc.mkRefl,calc.mkNat),calc.mkZero));
	evaluateAndTypeTest("""subst Nat 0 0 (I Nat 0) (refl Nat 0) (refl Nat 0)""", calc.mkApp(calc.mkApp(calc.mkApp(calc.mkI,calc.mkNat),calc.mkZero),calc.mkZero),
			calc.mkApp(calc.mkApp(calc.mkRefl,calc.mkNat),calc.mkZero));
	evaluateAndTypeTest("""let plus : Nat -> Nat -> Nat = natInd (\n: Nat. Nat -> Nat) (\x : Nat. x) (\n:Nat.\h:Nat -> Nat.\v:Nat.succ (h v)) in
			subst Nat 0 (plus 0 0)""", 
			calc.mkPi("P",calc.mkPi("A",calc.mkNat,calc.mkSet),
					calc.mkPi("eqPrf",calc.mkApp(calc.mkApp(calc.mkApp(calc.mkI,calc.mkNat),calc.mkZero),calc.mkZero),
							calc.mkPi("px",calc.mkApp(calc.mkVar(1),calc.mkZero),
									calc.mkApp(calc.mkVar(2),calc.mkZero)))),
									null);
		//test 62
	evaluateAndTypeTest("""let plus : Nat -> Nat -> Nat = natInd (\n: Nat. Nat -> Nat) (\x : Nat. x) (\n:Nat.\h:Nat -> Nat.\v:Nat.succ (h v)) in
			let eqprf : I Nat 0 (plus 0 0) = refl Nat 0 in
			let eqprf2 : I Nat 0 0 = refl Nat 0 in
			let eqprf3 : I Nat 0 (plus 0 0) = subst Nat 0 (plus 0 0) (I Nat 0) eqprf eqprf2 in
			eqprf3""", calc.mkApp(calc.mkApp(calc.mkApp(calc.mkI,calc.mkNat),calc.mkZero),calc.mkZero),
			calc.mkApp(calc.mkApp(calc.mkRefl,calc.mkNat),calc.mkZero));
	
	evaluateAndTypeTest("""
	    let plus : Nat -> Nat -> Nat = natInd (\n: Nat. Nat -> Nat) (\x : Nat. x) (\n:Nat.\h:Nat -> Nat.\v:Nat.succ (h v)) in
	    let prf : (n : Nat) -> (m : Nat) -> (k : Nat) -> I Nat (plus n (plus m k)) (plus (plus n m) k) =
	    		natInd (\n : Nat. (m : Nat) -> (k : Nat) -> I Nat (plus n (plus m k)) (plus (plus n m) k))
					(\m : Nat. \k : Nat. refl Nat (plus m k)) 
	    			(\n : Nat. \hyp : (m : Nat) -> (k : Nat) -> I Nat (plus n (plus m k)) (plus (plus n m) k).
						 \m : Nat. \k: Nat. subst Nat (plus n (plus m k)) (plus (plus n m) k)
							(\t : Nat. I Nat (succ (plus n (plus m k))) (succ t)) (hyp m k) 
							(refl Nat (succ (plus n (plus m k))))) in
	    prf 2 3 1		
		""", calc.mkApp(calc.mkApp(calc.mkApp(calc.mkI, calc.mkNat), calc.mkNatLit(6)), calc.mkNatLit(6)), 
			calc.mkApp(calc.mkApp(calc.mkRefl, calc.mkNat), calc.mkNatLit(6)));
	// cleaner using cong..
		//test 64
	evaluateAndTypeTest("""
	    let plus : Nat -> Nat -> Nat = natInd (\n: Nat. Nat -> Nat) (\x : Nat. x) (\n:Nat.\h:Nat -> Nat.\v:Nat.succ (h v)) in
	    let cong : (A : Set) -> (x : A) -> (y : A) -> (B : Set) -> (f : A -> B) -> I A x y -> I B (f x) (f y) =
				\A : Set. \x : A. \y: A. \B : Set. \f : A -> B. \xisy : I A x y.
	               subst A x y (\t : A. I B (f x) (f t)) xisy (refl B (f x)) in
	    let prf : (n : Nat) -> (m : Nat) -> (k : Nat) -> I Nat (plus n (plus m k)) (plus (plus n m) k) =
	    		natInd (\n : Nat. (m : Nat) -> (k : Nat) -> I Nat (plus n (plus m k)) (plus (plus n m) k))
					(\m : Nat. \k : Nat. refl Nat (plus m k)) 
	    			(\n : Nat. \hyp : (m : Nat) -> (k : Nat) -> I Nat (plus n (plus m k)) (plus (plus n m) k).
						 \m : Nat. \k: Nat. cong Nat (plus n (plus m k)) (plus (plus n m) k) Nat (\x : Nat. succ x) (hyp m k)) in
	    prf 2 3 1		
		""", calc.mkApp(calc.mkApp(calc.mkApp(calc.mkI, calc.mkNat), calc.mkNatLit(6)), calc.mkNatLit(6)), 
			calc.mkApp(calc.mkApp(calc.mkRefl, calc.mkNat), calc.mkNatLit(6)));

	// forall n. n + 0 = n
	//test 66
	evaluateAndTypeTest(
	    """let plus : Nat -> Nat -> Nat = natInd (\n: Nat. Nat -> Nat) (\x : Nat. x) (\n:Nat.\h:Nat -> Nat.\v:Nat.succ (h v)) in
	       let prop : Nat -> Set = \ n:Nat. I Nat (plus n 0) n in
	       let prf : (n: Nat) -> prop n = """ + calc.proofTerm + """ 
	       in prf 1""", calc.mkApp(calc.mkApp(calc.mkApp(calc.mkI,calc.mkNat),calc.mkSucc(calc.mkZero)),calc.mkSucc(calc.mkZero)),
			calc.mkApp(calc.mkApp(calc.mkRefl,calc.mkNat),calc.mkSucc(calc.mkZero)));
                        	                       
}