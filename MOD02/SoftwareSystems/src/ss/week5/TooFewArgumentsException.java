package ss.week5;

public class TooFewArgumentsException extends WrongArgumentException{
    @Override
    public String getMessage() {
        return "Argument should not be null!";
    }
}
