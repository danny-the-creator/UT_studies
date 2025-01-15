import java.util.concurrent.*;

class Count extends Thread {

    public int inc;
    public Count(int inc) {
        this.inc = inc;
    }

    static int ctr = 0;
    static boolean SEM;
    static Semaphore s = new Semaphore(1);

    public void run() {
        int loc;
        for(int i = 1; i <= 10; i++) {
            if(SEM) {
                try { s.acquire(); }
                catch(InterruptedException e) {}
            }
            loc = ctr + inc;
            System.out.println(inc + "\t" + loc);
            ctr = loc;
            if(SEM) {
                s.release();
            }
        }
    }

    public static void main(String [] args) {
        Count p = new Count(1);
        Count q = new Count(-1);
        SEM = args.length > 0 ;
        System.out.println("inc\tctr\tSEM="+SEM+"\n");
        p.start();
        q.start();
        try { p.join(); q.join(); }
        catch(InterruptedException e) { }
	    System.out.println("Final value ctr="+ctr);
        assert ctr == 0 ;
    }
}
