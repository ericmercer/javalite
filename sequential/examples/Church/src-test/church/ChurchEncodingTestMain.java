package church;

import LambdaTerm.Add1;
import LambdaTerm.LambdaTerm;
import LambdaTerm.SetIfNotZero;

public class ChurchEncodingTestMain {
	
	boolean man_exp2_3_ans = false;

	public static void main(String[] args) {
		ChurchEncodingTestMain ce = new ChurchEncodingTestMain();
		ce.run();
	}


	
	private void run() {
		Church c = new Church();
		LambdaTerm tmp;
		tmp = c.one();
		LambdaTerm two = c.plus(c.one(), c.one());
		Add1 add1 = new Add1();
		add1.doEval(tmp);
		System.out.println("Should be 1: " + add1.sum);
		add1.sum = 0;
		add1.doEval(c.succ(c.zero));
		System.out.println("Should be 1: " + add1.sum);
		add1.sum = 0;
		add1.doEval(c.zero());
		System.out.println("Should be 0: " + add1.sum);
		add1.sum = 0;
		add1.doEval(c.exp(two, c.plus(c.one(), two)));
		System.out.println("Should be 8: " + add1.sum);
		add1.sum = 0;
		add1.doEval(c.mult(two, c.plus(c.one(),two)));
		System.out.println("Should be 6: " + add1.sum);
		add1.sum = 0;
		add1.doEval(c.pred(two));
		System.out.println("Should be 1: " + add1.sum);

		LambdaTerm three = c.succ(two);
		LambdaTerm nine = c.mult(three, three);
		LambdaTerm eight = c.exp(two, c.plus(c.one(), two));
		add1.sum = 0;
		add1.doEval(c.minus(nine, eight));
		System.out.println("Should be 1: " + add1.sum);
		System.out.println(c.isZero(c.zero()).eval());
		
		SetIfNotZero sinz = new SetIfNotZero();
		sinz.bam = false;
		sinz.doEval(c.zero());
		System.out.println("Should be false:" + sinz.bam);
		sinz.bam = false;
		sinz.doEval(c.plus(c.one(),two));
		System.out.println("Should be true:" + sinz.bam);
		sinz.bam = false;
		sinz.doEval(c.minus(nine, eight));
		System.out.println("Should be true:" + sinz.bam);
		sinz.bam = false;
		sinz.doEval(c.minus(nine, nine));
		System.out.println("Should be false:" + sinz.bam);
	  }
	
}
