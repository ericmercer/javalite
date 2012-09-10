
public class Swap {

    public boolean boolFalse;
    public boolean boolTrue;
    
    public Swap() {
        boolFalse = false;
        boolTrue = true;
    }
    
    public void swap() {
        boolean tmp = boolTrue;
        boolTrue = boolFalse;
        boolFalse = tmp;
    }
}
