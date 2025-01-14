package ss.week1;

public class BrokenFibonacci {
    /**
     * Calculates the nth number in the fibonacci sequence
     * using arrays to store every number.
     * @param n the index of the nth number in the sequence
     * @return the nth fibonacci number
     */

    public static long fibonacci(int n) {
        if (n < 2) {
            return n;
        } else {
            long[] array = new long[n + 1];
//            array[0] = 1;
            array[1] = 1;
            for (int i = 2; i <= n; i++) {
                array[i] = array[i - 1] + array[i - 2];
            }
            return array[n];
        }
    }
}
