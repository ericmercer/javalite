package church;

import LambdaTerm.Abstraction;
import LambdaTerm.Application;
import LambdaTerm.LambdaTerm;
import LambdaTerm.Variable;

public class Church {

	protected final LambdaTerm zero;
	protected final LambdaTerm one;
	protected final Abstraction plus;
	protected final Abstraction succ;
	protected final Abstraction mult;
	protected final Abstraction exp;
	protected final Abstraction pred;
	protected final Abstraction minus;
	protected final Abstraction omega;
	protected final Abstraction identity;
	
	public Church() {
		Variable x = new Variable("x");
		Variable f = new Variable("f");
		Variable m = new Variable("m");
		Variable n = new Variable("n");
		Variable g = new Variable("g");
		Variable h = new Variable("h");
		Variable u = new Variable("u");
		
		zero = new Abstraction(f, new Abstraction(x, x));
		
		succ = new Abstraction(n,
					new Abstraction(f,
							new Abstraction(x,
									new Application(
											f,
											new Application( 
													new Application(n, f),
													x)))));
		
		plus = new Abstraction(m,
					new Abstraction(n,
							new Abstraction(f,
									new Abstraction(x,
											new Application(
													new Application(m, f),
													new Application(
														new Application(n, f), 
														x))))));
	
		mult = new Abstraction(m,
			      new Abstraction(n,
			         new Abstraction(f, 
			            new Abstraction(x,
			            		new Application( 
			            				new Application(m,
			            	               new Application(n, f)),
			            	            x)))));
					            
		exp = new Abstraction(m, 
					new Abstraction(n,
							new Application(n, m)));
		
		pred = new Abstraction(n,
			      new Abstraction(f,
			         new Abstraction(x,
			            new Application(
			               new Application(
			        	      new Application(
			                     n,
			                     new Abstraction(g,
			                        new Abstraction(h,
			                           new Application(
			                              h,
			                              new Application(g, f))))),
			                  new Abstraction(u, x)),
			               new Abstraction(u, u)))));   
			         
		minus = new Abstraction(m, 
				   new Abstraction(n,
				      new Application(
				         new Application(n, pred),
				         m)));
		
		//one = new Application(this.succ, zero);
		one = new Abstraction(f,
				new Abstraction(x,
				   new Application(f, x)));

		//two = (Abstraction) succ.br(one);
		
		omega = new Abstraction(g,
				   new Application(
				      new Abstraction(
							x,
							new Application(x,x)),
					  new Abstraction(
							x,
							new Application(x,x))));
		
		identity = new Abstraction(x,x);
	}
	

//	public Abstraction succ() {
//		return succ;
//	}
//	
//	public Abstraction plus() {
//		return plus;
//	}
//	
//	public Abstraction mult() {
//		return mult;
//	}
//	
//	public Abstraction exp() {
//		return exp;
//	}
//	
//	public Abstraction pred() {
//		return pred;
//	}
//	
//	public Abstraction minus() {
//		return minus;
//	}

	public LambdaTerm zero(){
		return zero;
	}
	
	public LambdaTerm one() {
		return one;
	}

//	public LambdaTerm two() {
//		return two;
//	}
	
	public LambdaTerm plus(LambdaTerm m, LambdaTerm n){
		return new Application((new Application(this.plus, m)), n);
	}
	
	public LambdaTerm succ(LambdaTerm n){
		return (new Application(this.succ, n));
	}
	
	public LambdaTerm mult(LambdaTerm m, LambdaTerm n){
		return (new Application((new Application(this.mult, m)), n));
	}
	
	public LambdaTerm exp(LambdaTerm m, LambdaTerm n){
		return (new Application((new Application(this.exp, m)), n));
	}
	
	public LambdaTerm pred(LambdaTerm n){
		return (new Application(this.pred, n));
	}

	public LambdaTerm minus(LambdaTerm m, LambdaTerm n){
		return new Application((new Application(this.minus, m)), n);
	}

	public LambdaTerm isZero(LambdaTerm m) {
		return (new Application((new Application(m, omega)), identity));
	}
}
