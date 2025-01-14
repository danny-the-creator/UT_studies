package ss.week1;
import java.util.Scanner;
import java.lang.Math;
public class PI {
    public static void main(String[] args) {
        System.out.println("Write a number of iterations");
        Scanner input = new Scanner(System.in);
        int N = input.nextInt();
        double n = 0;
        double x = 0;
        double y = 0;
        for (int counter = 1; counter < N; counter++){
            x = Math.random();
            y = Math.random();
            if (x*x + y*y <= 1){
                n++;
            }
        }
        System.out.println("Estimation of PI: "+ 4*n/N);
    }
}
