package LambdaTerm;

public class Application extends LambdaTerm {
	public static final boolean DEBUG = false;

	public LambdaTerm t;
	public LambdaTerm s;
	
	public Application(LambdaTerm t, LambdaTerm s) {
		this.t = t;
		this.s = s;
	}
	
	public LambdaTerm cas(Variable x, LambdaTerm r) {
		LambdaTerm lop = null;
		LambdaTerm rop = null;
		LambdaTerm v = null;
		
		if (DEBUG)
			System.out.println("Application: this = " + this + "   x = " + x + "   r = " + r);			
		
		lop = this.t.cas(x, r);
		rop = this.s.cas(x, r);
		v = new Application(lop, rop);
		
		if (DEBUG)
			System.out.println("cas(x,r) =" + v);
		
		return v;
	}

	public boolean isFree(Variable x) {
		boolean v = t.isFree(x);
		if (s.isFree(x))
			v = true;
		return v;
	}
	
	public String toString() {
		return ("(" + t.toString() + " " + s.toString() + ")");
	}

	@Override
	protected LambdaTerm ar(Variable oldVar, Variable newVar) {
		return new Application(t.ar(oldVar, newVar), s.ar(oldVar, newVar));
	}

	public boolean isAe(LambdaTerm x) {
		boolean v = false;
		Application a;
		
		if (x instanceof Application) {
			a = (Application)x;
			v = this.t.isAe(a.t) && this.s.isAe(a.s);
		}
		
		return v;
	}

	public LambdaTerm eval() {
		LambdaTerm lop = t.eval();
		LambdaTerm rop = s.eval();
		LambdaTerm v = null;
		
		if (lop instanceof Abstraction) {
			Abstraction a = (Abstraction)lop;
			v = a.br(rop).eval();
		} else {
			v = new Application(lop, rop);
		}

		return v;
	}

}
