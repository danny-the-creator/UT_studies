package ss.project.game.model;
/**
 * A player of the dotes and boxes game. Implements all the methods of the interface,
 * which are common for all the players.
 * If an object represents a player for a Dotes and Boxes game, it should implement this interface..
 */
public abstract class AbstractPlayer implements Player {
    private final String name;
    private final String colour;
    /**
     * Creates a new Player object.
     */
    /*@ requires name != null;
        ensures getName() == name;
    @*/
    public AbstractPlayer(String name, String colour) {
        this.name = name;
        this.colour = colour;
    }

    /**
     * Returns the name of the player.
     * @return the name of the player
     */
    public String getName() {
        return name;
    }
    /**
     * Returns the name of the player.
     * @return the colour of the player
     */
    public String getColour(){return colour;}

    /**
     * Determines the next move, if the game still has available moves.
     * Has to be implemented in a class
     * @param game the current game
     * @return the player's choice
     */
    //@ requires !game.isGameover();
    //@ ensures game.isValidMove(\result);
    @Override
    public abstract Move determineMove(Game game);
//    public abstract Move determineMove(Game game, String move) throws NotValidMove, NumberFormatException;

    /**
     * Returns a representation of a player, i.e., their name colored in their color
     * @return the String representation of this object
     */
    @Override
    public String toString() {
        return "Player " + getColour()+name+ Components.RESET;
    }

}
