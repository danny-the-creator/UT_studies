package ss.tictactoe.model;

/**
 * A move in a turn-based game.
 */
public interface Move {
    int getLocation();
    Mark getMark();
}
