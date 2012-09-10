package LambdaTerm;

public class Variable extends LambdaTerm {
	public static final boolean DEBUG = false;

	public String s;
	
	public Variable() {
	}
	
	public Variable(String s) {
		this.s = s;
	}
	
	public LambdaTerm cas(Variable x, LambdaTerm r) {
		LambdaTerm v = this;
		if (DEBUG) 
			System.out.println("this = " + this + "   x = " + x + "   r = " + r);			
		if (this == x) {
			v = r;
		}
		if (DEBUG)
			System.out.println("cas(x,r) = " + v);
		return v;
	}

	public boolean isFree(Variable x) {
		boolean v = false;
		if (x == this)
			v = true;
		return v;
	}
	
	public String toString() {
		return s;
	}

	protected LambdaTerm ar(Variable oldVar, Variable newVar) {
		LambdaTerm v = this;
		
		if (oldVar == this) {
			v = newVar;
		}
		
		return v;
	}

	public boolean isAe(LambdaTerm x) {
		return x == this;
	}

	@Override
	public LambdaTerm eval() {
		return this;
	}

}
