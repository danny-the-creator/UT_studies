// Press Shift twice to open the Search Everywhere dialog and type `show whitespaces`,
// then press Enter. You can now see whitespace characters in your code.
public class Main {
    private static int parseIP(String ipString) {
        String[] ipParts = ipString.split("\\.");

        int ip = 0;
        for (int i = 0; i < 4; i++) {
            ip |= Integer.parseInt(ipParts[i]) << (24 - (8 * i));
        }

        return ip;
    }
    public static void main(String[] args) {
        // Press Alt+Enter with your caret at the highlighted text to see how
        // IntelliJ IDEA suggests fixing it.
        System.out.print(parseIP("1.0.19.6")>>>1);

    }
}