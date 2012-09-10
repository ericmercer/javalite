package LambdaTerm;


public class Add1 implements Function {
	
	protected final static Variable x = new Variable();
	protected final static Variable y = new Variable();

	public int sum;

	public Add1() {
		sum = 0;
	}
	
	public void eval() {
		sum += 1;
	}
	
	public void doEval(LambdaTerm c) {
		(new Application (
		    new Application(c, new Abstraction(x, this)),
		    new Abstraction(y,y))).eval();
	}
	
}
