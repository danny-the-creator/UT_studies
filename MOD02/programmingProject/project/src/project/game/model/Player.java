package project.game.model;

/**
 * A player of a turn-based game. The interface on purpose does not contain any methods.
 * If an object represents a player for a game, it should implement this interface.
 * All the methods are described in "AbstractPlayer".
 */
public interface Player {
    String getName();

    String getColour();

    Move determineMove(Game game);
}
