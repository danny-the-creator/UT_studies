package ss.tictactoe.model;

/**
 * A player of a game.
 */
public abstract class AbstractPlayer implements Player {
    private final String name;
    private final Mark mark;
    /**
     * Creates a new Player object.
     */
    /*@ requires name != null;
        ensures getName() == name;
    @*/
    public AbstractPlayer(String name, Mark mark) {
        this.name = name;
        this.mark = mark;
    }

    /**
     * Returns the name of the player.
     * @return the name of the player
     */
    public String getName() {
        return name;
    }
    public Mark getMark(){return mark;}

    /**
     * Determines the next move, if the game still has available moves.
     * @param game the current game
     * @return the player's choice
     */
    //@ requires !game.isGameover();
    //@ ensures game.isValidMove(\result);
    public abstract Move determineMove(Game game);

    /**
     * Returns a representation of a player, i.e., their name
     * @return the String representation of this object
     */
    @Override
    public String toString() {
        return "Player " + name;
    }
}
