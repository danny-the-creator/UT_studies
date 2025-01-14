package project.game.model;

/**
 * A move in a turn-based game.
 */
public interface Move {
    /**
     * Where the chosen colour should be placed.
     * @return the location of this move.
     */
    int getLocation();

    /**
     * Which colour should be placed on the chosen location.
     * @return the colour of this move
     */
    String getColour();
}
