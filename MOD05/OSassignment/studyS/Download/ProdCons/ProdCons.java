public class ProdCons {
   public static void main(String [] args) {
       Buffer B = new Buffer(4);
       Prod P = new Prod(B);
       Cons C = new Cons(B);
       P.start();
       C.start();
   }
}
