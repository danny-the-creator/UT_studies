package ss.week1;
import java.util.Arrays;
import java.util.Scanner;
public class SplitNumbers {
    public static void sort(int[] a){}
    public static void main(String[] args) {
        System.out.println("Please enter some numbers:");
        Scanner input = new Scanner(System.in);
        String word = input.nextLine();
        String[] split = word.split("\\s+");

        int[] numbers = new int[split.length];
        for (int i = 0; i < split.length; i++) {
            numbers[i] = Integer.parseInt(split[i]);
        }
        Arrays.sort(numbers);
        for (int num : numbers) {
            System.out.print(num + " ");
        }
    }
}
