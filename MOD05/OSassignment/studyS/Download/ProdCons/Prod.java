class Prod extends Thread {
    private Buffer buffer;
     
    Prod(Buffer b) {
        buffer = b;
    }

    public void run() {
        for(int i = 0; i < 10; i++) {
            buffer.Put(i);
        }
    }
}    
