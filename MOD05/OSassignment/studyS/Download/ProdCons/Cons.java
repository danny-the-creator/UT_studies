class Cons extends Thread {
    private Buffer buffer;
   
    Cons(Buffer b) {
        buffer = b;
    }

    public void run() {
        for(int i = 0; i < 10; i++) {
            int k = buffer.Get();
            assert(i == k) ;
        }
    }
}   
