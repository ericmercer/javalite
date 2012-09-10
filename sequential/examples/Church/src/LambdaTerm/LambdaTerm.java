package LambdaTerm;

public abstract class LambdaTerm {
	
	// captureAvoidingSubstitution
	public abstract LambdaTerm cas(Variable x, LambdaTerm r);
	
	public abstract boolean isFree(Variable x);
	
	// AlphaEquivalent
	public abstract boolean isAe(LambdaTerm x);
	
	// AlphaReduce
	protected abstract LambdaTerm ar(Variable oldVar, Variable newVar);
	
	// Evaluate the lambda term (i.e., reduce maximally)
	public abstract LambdaTerm eval();
}
