package ss.hotel.password;

public class BasicPassword {
    public static final String INITIAL = "000000";
    private String password;

    public BasicPassword() {
        this.password = INITIAL;
    }

    public boolean acceptable(String suggestion) {
        if ((suggestion.length() < 6) || (suggestion.split(" ").length != 1)) {
            return false;
        }
        return true;
    }

    public boolean testWord(String test) {
        if (this.password.equals(test)) {
            return true;
        }
        return false;
    }

    public boolean setWord(String oldpass, String newpass) {
        if (!testWord(oldpass)) {
            System.out.println("Wrong password");
            return false;
        }
        if (!acceptable(newpass)) {
            System.out.println("Password is not acceptable");
            return false;
        }
        this.password = newpass;
        return true;
    }
}