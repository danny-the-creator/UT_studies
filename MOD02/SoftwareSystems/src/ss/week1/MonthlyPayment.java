package ss.week1;
import java.util.Scanner;
import java.lang.Math;
public class MonthlyPayment {
    public static void main(String[] args) {
        System.out.println("Write the amount borrowed");
        Scanner input = new Scanner(System.in);
        int p = input.nextInt();
        System.out.println("Write the yearly interest rate");
        double r = input.nextDouble();
        System.out.println("Write the number of years");
        int n = input.nextInt();
        r = r / 1200;
        n = n * 12;
        System.out.println("The monthly payment is " + Math.round(r/ (1 - Math.pow((1 + r), (-1*n))) * p ));
    }
}
