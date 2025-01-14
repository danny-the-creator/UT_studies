package ss.week1;

import java.util.Scanner;

public class emirp {
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
    /**
     * Check if the given number is emirp
     * @param number
     * @return true if the number is emirp and false if the number is not emirp
     */
    public static boolean isEmir (int number){

        boolean first = isPrime(number);
        int number1 = number;
        int rest = 0;
        String num = "";
        while (number!=0) {
            rest = number % 10;
            num += rest;
            number = number / 10;
        }
        boolean second = isPrime(Integer.parseInt(num));
        //            System.out.println(second);
        if (number1 == Integer.parseInt(num)){
            return false;
        };
        return first && second;
    }

    public static void main(String[] args) {
        System.out.println("How many emirps?");
        Scanner input = new Scanner(System.in);
        int num = input.nextInt();
        int counter = 2;
        int counter1 = 1;
        StringBuilder text = new StringBuilder("Emirps: ");
        while (counter1 <= num){
            if (isEmir(counter)) {
                text.append(counter).append(" ");
                counter1++;
            }
            counter++;
        }
        System.out.println(text);
    }
}

