package ss.hotel.password;

public class Password {
    private String password;
    private Checker checker;
    private String initPass;
    //@ensures initPass != null;
    public String getInitPass() {
        return initPass;
    }
    //@ensures checker != null;
    public Checker getChecker() {
        return checker;
    }

    //@ requires checker != null;
    //@ ensures this.initPass != null && this.password.equals(this.initPass) && this.checker == checker;
    public Password(Checker checker){
        this.initPass = checker.generatePassword();
        this.password = this.initPass;
        this.checker = checker;
    }
    public Password(){
        this(new BasicChecker());
    }
    //@ requires suggestion!= null;
    //@ ensures \result == true ==> suggestion.length()>=6 && suggestion.split(" ").length == 1;
    public boolean acceptable(String suggestion){
        if ((suggestion.length()<6) || (suggestion.split(" ").length != 1)){
            return false;
        }
        return true;
    }
    //@requires test != null;
    //@ensures \result == true <==> this.password.equals(test);
    public boolean testWord(String test){
        return this.password.equals(test);
    }

    //@requires oldpass!= null && newpass != null;
    //@ ensures \result == true ==> testWord(oldpass) && acceptable(newpass);
    public boolean setWord(String oldpass, String newpass){
        if (!testWord(oldpass)){
            System.out.println("Wrong password");
            return false;
        }
        if (!acceptable(newpass)){
            System.out.println("Password is not acceptable");
            return false;
        }
        this.password = newpass;
        return true;
    }
}
