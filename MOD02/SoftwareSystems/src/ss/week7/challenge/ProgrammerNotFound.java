package ss.week7.challenge;

public class ProgrammerNotFound extends Exception{
    ProgrammerNotFound(String name){
        System.out.println("Programmer "+name +" not found!");
    }
}
