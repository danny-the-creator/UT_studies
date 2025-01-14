package ss.week5;

public class ArgumentLengthsDifferException extends WrongArgumentException{
    int n1,n;
    public ArgumentLengthsDifferException(int i, int i1) {
        n = i;
        n1 = i1;
    }
    @Override
    public String getMessage() {
        return "Size of the lists should be equal! \nFirst length: "+ n + "\n" + "Second length: " + n1;
    }
}
