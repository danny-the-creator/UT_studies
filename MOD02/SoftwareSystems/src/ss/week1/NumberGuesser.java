package ss.week1;
import java.util.Scanner;
import java.lang.Math;
public class NumberGuesser {
    public static void main(String[] args) {
        long my_num = Math.round(Math.random()*100);
    while (true){
        System.out.println("Guess my number!");
        Scanner input = new Scanner(System.in);
        int num = input.nextInt();
        if (num > my_num){
            System.out.println("Too high!");
        }
        else if (num< my_num){
            System.out.println("Too low!");
        }
        else {
            System.out.println("Yeah, you did it! \nGood job!");
            break;
        }
    }
    }
}
