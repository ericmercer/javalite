package church;

import junit.framework.Test;
import junit.framework.TestCase;
import junit.framework.TestSuite;
import LambdaTerm.Abstraction;
import LambdaTerm.Add1;
import LambdaTerm.LambdaTerm;
import LambdaTerm.SetIfNotZero;
import LambdaTerm.Variable;


public class ChurchEncodingTest extends TestCase{

	  Church instance;
	  LambdaTerm three;
	  LambdaTerm two;
	  LambdaTerm five;
	  Add1 add1;
	  SetIfNotZero sinz;
	  
	  public ChurchEncodingTest(String testName) {
	    super(testName);
	    Church v = new Church();
	    this.instance = v;
	    this.two = v.plus(v.one(), v.one());
	    this.three = v.plus(v.one(), this.two);
	    this.five = v.plus(this.three, this.two);
	    this.add1 = new Add1();
	    this.sinz = new SetIfNotZero();
	  }
	  
	  public static Test suite() {
	    TestSuite suite = new TestSuite(ChurchEncodingTest.class);
	    
	    return suite;
	  }
	  
	  public void testArBasic() throws Exception {
		  Variable x = new Variable("x");
		  Variable y = new Variable("y");
		  Abstraction lx = new Abstraction(x, x);		  
		  Abstraction ans = 
		  	  new Abstraction(y,y);
		  
		  assertTrue((new Abstraction(x, x)).isAe(new Abstraction(y, y)));
		  assertTrue(lx.isAe(ans));
	  }
	  
	  public void testArShadowed() throws Exception {
		  Variable x = new Variable("x");
		  Variable y = new Variable("y");
		  Abstraction lx = new Abstraction(x, new Abstraction(x, x));
		  
		  String s = "yx.x";
		  
		  assertTrue(s.equals(lx.arAbstraction(y).toString()));
	  }
	  
	  public void testArDiffAbstraction() throws Exception {
		  Variable x = new Variable("x");
		  Variable y = new Variable("y");
		  Abstraction lx = new Abstraction(x, new Abstraction(y, x));
		  LambdaTerm v = lx.arAbstraction(y);
		  assertTrue(lx.isAe(v));
	  }
	  
	  public void testZero() throws Exception {
		  add1.sum = 0;
		  add1.doEval(instance.zero());
		  assertTrue(add1.sum == 0);
	  }

	  public void testZeroJavalite() throws Exception {
		  Church c = this.instance;
		  SetIfNotZero s = this.sinz;
		  s.bam = false;
		  s.doEval(c.zero());
		  assertTrue(s.bam == false);
	  }
	  
	  public void testNotZeroJavalite() throws Exception {
		  Church c = this.instance;
		  SetIfNotZero s = this.sinz;
		  s.bam = false;
		  s.doEval(c.one());
		  assertTrue(s.bam == true);
	  }
	  
	  public void testOne() throws Exception {
		  add1.sum = 0;
		  add1.doEval(instance.one());
		  assertTrue(add1.sum == 1);
	  }

	  public void testTwo() throws Exception {
		  add1.sum = 0;
		  add1.doEval(this.two);
		  assertTrue(add1.sum == 2);
	  }

	  public void testPlus() throws Exception {
		  add1.sum = 0;
		  add1.doEval(five);
		  assertTrue(add1.sum == 5);
	  }

	  public void testMinus() throws Exception {
		  add1.sum = 0;
		  add1.doEval(instance.minus(instance.plus(two,three),five));
		  assertTrue(add1.sum == 0);
	  }
	  	  
	  public void test1plus2() throws Exception {
		  add1.sum = 0;
		  add1.doEval(instance.plus(instance.one(), two));
		  assertTrue(add1.sum == 3);		  
	  }

	  public void test3plus2() throws Exception {
		  add1.sum = 0;
		  add1.doEval(instance.minus(instance.plus(three, two), five));
		  assertTrue(add1.sum == 0);		  
	  }
	  
	  public void test3mult2() throws Exception {
		  add1.sum = 0;
		  add1.doEval(instance.mult(two,three));
		  assertTrue(add1.sum == 6);		  
	  }

	  public void test2exp3() throws Exception {
		  add1.sum = 0;
		  add1.doEval(instance.exp(two, three));
		  assertTrue(add1.sum == 8);		  
	  }

	  public void testIsZero() throws Exception {
		  LambdaTerm r = instance.isZero(instance.minus(instance.plus(three, two), five)).eval();
		  assertTrue(r.toString().equals("x.x"));
	  }
	  
	  public void testJavalite3plus2() throws Exception {
		  sinz.bam = false;
		  LambdaTerm five = instance.plus(two, three);
		  sinz.doEval(instance.minus(five, five));
		  assertFalse(sinz.bam);
	  }
	  
	  public void testJavaliteVariableEquivalence() throws Exception {
		  Variable x = new Variable();
		  Variable y = new Variable();
		  assertFalse(x == y);
	  }
}
