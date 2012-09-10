package LambdaTerm;


public class Abstraction extends LambdaTerm {	
	public static final boolean DEBUG = false;
	public static int count = 0;
	
	public LambdaTerm t;
	public Variable x;
	public Function f;
	
	public Abstraction(Variable x, LambdaTerm t) {
		this.t = t;
		this.x = x;
		this.f = null;
	}

	public Abstraction(Variable x, Function f) {
		this.t = x;
		this.x = x;
		this.f = f;
	}
	
	protected Abstraction(Variable x, LambdaTerm t, Function f) {
		this.t = t;
		this.x = x;
		this.f = f;
	}
	
	@SuppressWarnings("static-access")
	public LambdaTerm cas(Variable x, LambdaTerm r) {
		LambdaTerm v = null;
		Variable y = this.x;
		Variable z = null;
		
		if (DEBUG)
			System.out.println("Abstraction: this = " + this + "   x = " + x + "   r = " + r);
		
		if (x == y) {
			v = this;
		} else if (r.isFree(y) == false) {
			// y is not a free variable in r
			v = new Abstraction(y, t.cas(x, r), f);
		} else {
			// y is a free variable in r -- alpha-rename
			z = new Variable("z" + this.count++);
			v = new Abstraction(z, this.t.ar(y, z).cas(x, r), f);
		}

		if (DEBUG)
			System.out.println("cas(x,r) = " + v);

		return v;
	}

	public boolean isFree(Variable x) {
		boolean v = false;
		if ((x != this.x) && t.isFree(x))
			v = true;
		return v;
	}

	public LambdaTerm br(LambdaTerm s) {
		LambdaTerm v = this.t.cas(this.x, s);
		if (f != null)
			f.eval();
		return v;
	}

	public LambdaTerm arAbstraction(Variable x) {
		Variable y = this.x;
		
		return new Abstraction(x, this.t.ar(y, x), f);
	}
	
	
	public String toString() {
		String rv = this.x.toString();
		if (this.t instanceof Abstraction) {
			rv += this.t;
		} else {
			rv += "." + this.t;
		}	
		return rv;
	}

	@SuppressWarnings("static-access")
	@Override
	protected LambdaTerm ar(Variable oldVar, Variable newVar) {
		LambdaTerm v = null;
		Variable y = this.x;
		Variable z;
		
		if (y == oldVar) {
			v = this;
		} else if (y == newVar) {
			z = new Variable("z" + this.count++);
			v = this.arAbstraction(z).ar(oldVar, newVar);
		} else {
			v = new Abstraction(this.x, this.t.ar(oldVar, newVar), f);
		}
		
		return v;
	}

	public boolean isAe(LambdaTerm x) {
		boolean v = false;
		Abstraction a;
		
		if (x instanceof Abstraction) {
			a = (Abstraction) x;
			if (this.x.isAe(a.x) == false) {
				a = (Abstraction) a.arAbstraction(this.x);
			}
			
			v = this.t.isAe(a.t);
		}
		
		return v;
	}

	public LambdaTerm eval() {
		return this;
	}

}
