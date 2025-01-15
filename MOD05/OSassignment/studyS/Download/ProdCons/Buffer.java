class Buffer{
    private int []B;
    private int Cnt = 0, In = 0, Out = 0;

    Buffer(int size) {
       B = new int[size];
    }

    public synchronized void Put(int i) {
        while(Cnt == B.length) {
            try{ wait(); }
            catch(InterruptedException e) { }
            finally{ }
        }
        B[In] = i;
        System.out.println("    B[" + In + "]=" + i);
        In = (In + 1) % B.length;
        Cnt++;
        notify();
    }

    public synchronized int Get() {
        while(Cnt == 0) {
            try{ wait(); }
            catch(InterruptedException e) { }
            finally{ }
        }
        int i = B[Out];
        System.out.println(i + "=B[" + Out + "]");
        Out = (Out + 1) % B.length;
        Cnt--;
        notify();
        return i;
    }
}
