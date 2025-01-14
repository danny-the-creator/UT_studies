package ss.week1;
import java.util.Scanner;
public class prime_number {
    /**
     * Check if the given number is Prime
     * @param number
     * @return true if the number is prime and false if the number is not prime
     */
    public static boolean isPrime (int number){
        for (int count = 2; count<= (number/2); count++){
            if (number % count == 0){
                return false;
            }
        }
        return true;
    }
    public static void main(String[] args) {
        System.out.println("How many primes?");
        Scanner input = new Scanner(System.in);
        int num = input.nextInt();
        int counter = 2;
        int counter1 = 1;
        StringBuilder text = new StringBuilder("Primes: ");
        while (counter1 <= num){
            if (isPrime(counter)) {
                text.append(counter).append(" ");
                counter1++;
            }
            counter++;
        }
        System.out.println(text);
    }
}
