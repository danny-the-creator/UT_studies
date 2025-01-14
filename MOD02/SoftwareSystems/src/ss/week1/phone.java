package ss.week1;
import java.util.Scanner;
public class phone {
    public static void main(String[] args) {
        System.out.println("Please enter a word:");
        Scanner input = new Scanner(System.in);
        String word = input.nextLine();
        word = word.toLowerCase();
        String num = "";
        int n = 0;
        char ch ='a';
        while (ch != word.toCharArray()[word.length()-1]){
            ch = word.toCharArray()[n];
            n+=1;
            switch (ch){
                case 'a':
                case 'b':
                case 'c':
                    num += '2';
                    break;
                case 'd':
                case 'e':
                case 'f':
                    num += '3';
                    break;
                case 'g':
                case 'h':
                case 'i':
                    num+='4';
                    break;
                case 'j':
                case 'k':
                case 'l':
                    num+='5';
                    break;
                case 'm':
                case 'n':
                case 'o':
                    num+='6';
                    break;
                case 'p':
                case '1':
                case 'r':
                case 's':
                    num+='7';
                    break;
                case 't':
                case 'u':
                case 'v':
                    num+='8';
                    break;
                case 'w':
                case 'x':
                case 'y':
                case 'z':
                    num+='9';
                    break;
                case ' ':
                    num+='0';
                    break;
            }
        }
        System.out.println(num);
    }

}
