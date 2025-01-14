package ss.week1;
import java.util.Scanner;
public class GrossAndDozens {
    public static void main(String[] args) {
        System.out.println("How many eggs?");
        Scanner input = new Scanner(System.in);
        int eggs = input.nextInt();
        System.out.println("Your number of eggs is "+eggs/144+" gross, "+(eggs%144)/12+" dozen, and "+eggs%12);
    }

}
