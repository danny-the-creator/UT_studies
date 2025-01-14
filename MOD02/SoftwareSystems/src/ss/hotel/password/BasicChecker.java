package ss.hotel.password;

class BasicChecker implements Checker {
    public boolean acceptable(String pattern){
        return (pattern.length() >= 6) && (pattern.split(" ").length == 1);
    }
}
