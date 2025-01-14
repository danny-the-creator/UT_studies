package ss.week1;
import java.util.Scanner;
import java.lang.Math;
public class math {
    public static void main(String[] args) {
        System.out.println("n = ?");
        Scanner input = new Scanner(System.in);
        int n = input.nextInt();
        System.out.println("s = ?");
        double s = input.nextDouble();
        System.out.println((n*s*s)/(4* Math.tan(Math.PI/n)));
    }
}
