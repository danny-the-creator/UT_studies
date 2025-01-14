package ss.week1;

import java.util.Scanner;

/**
 * Hello World class.
 */
public class Hello {
    /**
     * Prints a greeting to the console.
     * @param args command-line arguments; currently unused
     */
    public static void main(String[] args) {
        System.out.println("Name and Age?");
        Scanner input = new Scanner(System.in);
        java.lang.String a =input.nextLine();
        int x = input.nextInt();
        System.out.println("Hello "+a+", "+x);
    }
}