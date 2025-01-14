package ss.week1;
import java.util.Scanner;
public class Fibonacci {
    /**
     * Calculates the nth number in the fibonacci sequence
     * @param number
     * @return the fibonacci number which has an index n
     */
    public static long fibonacci(int number){
        if (number == 0){
            return 0;
        } else if (number==1){
            return 1;
        } else {
            return fibonacci(number - 1) + fibonacci(number - 2);
        }
    }
    public static void main(String[] args) {
        System.out.println("Enter your number:");
        Scanner input = new Scanner(System.in);
        int num = input.nextInt();
        System.out.println(fibonacci(num));
    }
}
