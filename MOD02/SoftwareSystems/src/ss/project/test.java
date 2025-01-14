package ss.project;

public class test {
    public static void main(String[] args) {
        int index  = -1;
        Character text = 'a';
        switch (text){
            case 'a' -> {
                System.out.println("1");
                System.out.println("2");
                if (index<0){
                    break;
                }
                System.out.println("3");
            }
            case 'b' -> {
                System.out.println("4");
                System.out.println("5");
                if (index<-100){
                    break;
                }
                System.out.println("6");
            }
            case 'c' -> {
                System.out.println("7");
                System.out.println("8");
                System.out.println("9");
            }
        }
    }
}
