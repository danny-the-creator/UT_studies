package ss.project.game.model;

/**
 * Represents the exception, which needs to be thrown if the move,
 * that player wants to make is illegal.
 */
public class NotValidMove extends Exception {
    public NotValidMove(){
        super("CANNOT PLAY THIS MOVE");
    }
}
