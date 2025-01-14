package ss.tictactoe.model;

/**
 * A player of a turn-based game. The interface on purpose does not contain any methods.
 * If an object represents a player for a game, it should implement this interface.
 */
public interface Player {
    public String getName();
    public Mark getMark();
    public Move determineMove(Game game);
}
