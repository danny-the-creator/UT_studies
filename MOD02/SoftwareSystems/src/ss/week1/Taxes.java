package ss.week1;
import java.util.Scanner;
public class Taxes {
    public static void main(String[] args) {
        System.out.println("What's your income?");
        Scanner input = new Scanner(System.in);
        double income = input.nextInt();
        double tax = 0;
        if (income <= 35472){
            tax = 0.0942* income;
        }
        else if (income <= 69398){
            tax = 3341+ 0.3707* (income - 35472);
        }
        else {
            tax =15917 + 0.4950 * (income - 69398);
        }
        System.out.println("Your income tax is "+ tax);
    }
}
