package LambdaTerm;


public class SetIfNotZero implements Function {
	
	protected final static Variable x = new Variable();
	protected final static Variable y = new Variable();

	public Boolean bam;

	public SetIfNotZero() {
		bam = false;
	}
	
	public void eval() {
		bam = true;
	}
	
	public void doEval(LambdaTerm c) {
		(new Application (
		    new Application(c, new Abstraction(this.x, this)),
		    new Abstraction(this.y, this.y))).eval();
	}
	
}
