package ss.hotel.password;

public interface Checker {
    /**
     *
     * @param pattern
     * @return false if length <6 or suggestion has a " " else true
     */
    //@ requires pattern != null;
    //@ ensures \result == true ==> pattern.length()>=6 && pattern.split(" ").length == 1;
     boolean acceptable(String pattern);

    //@ensures acceptable(\result);
    //@pure;
    public default String generatePassword(){
        return "default";
    }

}
