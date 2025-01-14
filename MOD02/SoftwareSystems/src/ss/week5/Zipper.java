package ss.week5;

public class Zipper {
	/**
	 * @return the zipped result String
	 */
    /*@ requires s1 != null & s2 != null;
    requires s1.length() == s2.length();
     @*/
    public static String zip(String s1, String s2) {
        String result = "";
        for (int i = 0; i < s1.length(); i++) {
            result += Character.toString(s1.charAt(i)) + Character.toString(s2.charAt(i));
        }
        return result;
    }
    public static String zip2(String s1, String s2) throws TooFewArgumentsException, ArgumentLengthsDifferException{
        if (s1 == null || s2 == null){
            throw new TooFewArgumentsException();
        }
        if (s1.length() != s2.length()) {
            throw new ArgumentLengthsDifferException(s1.length(), s2.length());
        }
        return zip(s1, s2);
    }

    public static void main(String[] args) throws TooFewArgumentsException, ArgumentLengthsDifferException {
        String s1 = "01234567";
        String s2 = "ffffffff";
        System.out.println(zip2(s1, s2));
    }
}
