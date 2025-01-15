import java.util.concurrent.*;

class MyThread extends Thread {

    static final int N = 50 ;
    int arg;

    public MyThread(int arg) {
        this.arg = arg;
    }

    public void run() {
       System.out.println("Thread " + arg);
    }

    public static void main(String [] args) {
        MyThread[] tid = new MyThread [N] ;
        for(int i = N-1; i >= 0; i--) {
            tid[i] = new MyThread(i*i);
            tid[i].start();
        }
        for(int i = 0; i < N; i++) {
            try { tid[i].join(); }
            catch(InterruptedException e) { }
        }
    }
}
