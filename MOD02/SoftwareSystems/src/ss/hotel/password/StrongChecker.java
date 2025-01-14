package ss.hotel.password;

class StrongChecker extends BasicChecker {
    private boolean StrongPass(String suggestion){
        return  acceptable(suggestion) && Character.isLetter(
                suggestion.charAt(0)) && Character.isDigit(
                suggestion.charAt(suggestion.length() - 1));
    }
}